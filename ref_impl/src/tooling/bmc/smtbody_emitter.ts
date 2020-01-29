//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIRInvokeDecl, MIRInvokeBodyDecl, MIRInvokePrimitiveDecl, MIRConstantDecl, MIRFieldDecl, MIREntityTypeDecl, MIREntityType, MIRTupleType, MIRRecordType, MIRRecordTypeEntry, MIRConceptType, MIRTupleTypeEntry, MIREpemeralListType } from "../../compiler/mir_assembly";
import { SMTTypeEmitter } from "./smttype_emitter";
import { MIRArgument, MIRRegisterArgument, MIRConstantNone, MIRConstantFalse, MIRConstantTrue, MIRConstantInt, MIRConstantArgument, MIRConstantString, MIROp, MIROpTag, MIRLoadConst, MIRAccessArgVariable, MIRAccessLocalVariable, MIRInvokeFixedFunction, MIRPrefixOp, MIRBinOp, MIRBinEq, MIRBinCmp, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRRegAssign, MIRTruthyConvert, MIRLogicStore, MIRVarStore, MIRReturnAssign, MIRJumpCond, MIRJumpNone, MIRAbort, MIRPhi, MIRBasicBlock, MIRJump, MIRConstructorTuple, MIRConstructorRecord, MIRAccessFromIndex, MIRAccessFromProperty, MIRInvokeKey, MIRAccessConstantValue, MIRLoadFieldDefaultValue, MIRBody, MIRConstructorPrimary, MIRBodyKey, MIRAccessFromField, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionSingletons, MIRIsTypeOf, MIRProjectFromIndecies, MIRModifyWithIndecies, MIRStructuredExtendTuple, MIRProjectFromProperties, MIRModifyWithProperties, MIRStructuredExtendRecord, MIRLoadConstTypedString, MIRConstructorEphemeralValueList, MIRProjectFromFields, MIRModifyWithFields, MIRStructuredExtendObject } from "../../compiler/mir_ops";
import { SMTExp, SMTValue, SMTCond, SMTLet, SMTFreeVar } from "./smt_exp";
import { SourceInfo } from "../../ast/parser";

import * as assert from "assert";
import { MIRKeyGenerator } from "../../compiler/mir_emitter";

function NOT_IMPLEMENTED<T>(msg: string): T {
    throw new Error(`Not Implemented: ${msg}`);
}

class SMTBodyEmitter {
    readonly assembly: MIRAssembly;
    readonly typegen: SMTTypeEmitter;

    private standard_gas = 4;
    private collection_gas = 5;
    private string_gas = 10;
    private regex_gas = 3;
    private api_pod_type_gas = 3;

    private errorCodes = new Map<string, number>();
    private gasLimits = new Map<string, number>().set("default", 4).set("collection", 5).set("string", 10).set("regex", 3).set("ap_type", 3);

    private currentFile: string = "[No File]";
    private currentRType: MIRType;
    private tmpvarctr = 0;
    private currentSCC = new Set<string>();

    private vtypes: Map<string, MIRType> = new Map<string, MIRType>();

    private subtypeOrderCtr = 0;
    subtypeFMap: Map<string, {order: number, decl: string}> = new Map<string, {order: number, decl: string}>();

    vfieldLookups: { arg: MIRArgument, infertype: MIRType, fdecl: MIRFieldDecl, lname: string }[] = [];
    vfieldProjects: { arg: MIRArgument, infertype: MIRType, fdecls: MIRFieldDecl[], pname: string }[] = [];
    vfieldUpdates: { arg: MIRArgument, infertype: MIRType, fupds: [MIRFieldDecl, MIRArgument][], uname: string }[] = [];
    vobjmerges: { arg: MIRArgument, infertype: MIRType, merge: MIRArgument, infermergetype: MIRType, fieldResolves: [string, MIRFieldDecl][], mname: string }[] = [];

    constructor(assembly: MIRAssembly, typegen: SMTTypeEmitter) {
        this.assembly = assembly;
        this.typegen = typegen;

        this.currentRType = typegen.noneType;
    }

    generateTempName(): string {
        return `@tmpvar@${this.tmpvarctr++}`;
    }

    generateErrorCreate(sinfo: SourceInfo, rtype: string): SMTValue {
        const errorinfo = `${this.currentFile} @ line ${sinfo.line} -- column ${sinfo.column}`;
        if (!this.errorCodes.has(errorinfo)) {
            this.errorCodes.set(errorinfo, this.errorCodes.size);
        }
        const errid = this.errorCodes.get(errorinfo) as number;

        return new SMTValue(`(result_error@${rtype} (result_error ${errid}))`);
    }

    getErrorIds(...sinfos: SourceInfo[]): number[] {
        const ekeys = sinfos.map((sinfo) => `${this.currentFile} @ line ${sinfo.line} -- column ${sinfo.column}`);
        return [...new Set<number>(ekeys.map((k) => this.errorCodes.get(k) as number))].sort();
    }

    getGasKeyForOperation(tkey: string): "collection" | "string" | "regex" | "ap_type" | "default" {
        if(tkey.startsWith("NSCore::List<") || tkey.startsWith("NSCore::Set<") || tkey.startsWith("NSCore::Map<")) {
            return "collection";
        }
        else if(tkey === "NSCore::String") {
            return "string";
        }
        else if(tkey === "NSCore::Regex") {
            return "regex";
        }
        else if(tkey === "TYPE_CHECK") {
            return "ap_type";
        }
        else {
            return "default";
        }
    }

    getGasForOperation(tkey: string): number {
        return this.gasLimits.get(this.getGasKeyForOperation(tkey)) as number;
    }

    generateBMCLimitCreate(tkey: string, rtype: string): SMTValue {
        const errid = this.getGasForOperation(tkey);
        return new SMTValue(`(result_error@${rtype} (result_bmc ${errid}))`);
    }

    varNameToSMTName(name: string): string {
        if (name === "_return_") {
            return "_return_";
        }
        else {
            return this.typegen.mangleStringForSMT(name);
        }
    }

    varToSMTName(varg: MIRRegisterArgument): string {
        return this.varNameToSMTName(varg.nameID);
    }

    invokenameToSMT(ivk: MIRInvokeKey): string {
        return this.typegen.mangleStringForSMT(ivk);
    }

    getArgType(arg: MIRArgument): MIRType {
        if (arg instanceof MIRRegisterArgument) {
            return this.vtypes.get(arg.nameID) as MIRType;
        }
        else {
            if (arg instanceof MIRConstantNone) {
                return this.typegen.noneType;
            }
            else if (arg instanceof MIRConstantTrue || arg instanceof MIRConstantFalse) {
                return this.typegen.boolType;
            }
            else if (arg instanceof MIRConstantInt) {
                return this.typegen.intType;
            }
            else {
                return this.typegen.stringType;
            }
        }
    }

    generateConstantExp(cval: MIRConstantArgument, into: MIRType): SMTExp {
        if (cval instanceof MIRConstantNone) {
            return this.typegen.coerce(new SMTValue("bsqkey_none"), this.typegen.noneType, into);
        }
        else if (cval instanceof MIRConstantTrue) {
            return this.typegen.coerce(new SMTValue("true"), this.typegen.boolType, into);
        }
        else if (cval instanceof MIRConstantFalse) {
            return this.typegen.coerce(new SMTValue("false"), this.typegen.boolType, into);
        }
        else if (cval instanceof MIRConstantInt) {
            return this.typegen.coerce(new SMTValue(cval.value), this.typegen.intType, into);
        }
        else {
            assert(cval instanceof MIRConstantString);

            return this.typegen.coerce(new SMTValue((cval as MIRConstantString).value), this.typegen.stringType, into);
        }
    }

    argToSMT(arg: MIRArgument, into: MIRType): SMTExp {
        if (arg instanceof MIRRegisterArgument) {
            return this.typegen.coerce(new SMTValue(this.varToSMTName(arg)), this.getArgType(arg), into);
        }
        else {
            return this.generateConstantExp(arg as MIRConstantArgument, into);
        }
    }

    generateTruthyConvert(arg: MIRArgument): SMTExp {
        const argtype = this.getArgType(arg);

        if (this.assembly.subtypeOf(argtype, this.typegen.noneType)) {
            return new SMTValue("false");
        }
        else if (this.assembly.subtypeOf(argtype, this.typegen.boolType)) {
            return this.argToSMT(arg, this.typegen.boolType);
        }
        else if (this.typegen.typecheckAllKeys(argtype)) {
            return new SMTValue(`(= ${this.argToSMT(arg, this.typegen.keyType).emit()} (bsqkey_bool true))`);
        }
        else {
            return new SMTValue(`(= ${this.argToSMT(arg, this.typegen.anyType).emit()} (bsqterm_key (bsqkey_bool true)))`);
        }
    }

    generateNoneCheck(arg: MIRArgument): SMTExp {
        const argtype = this.getArgType(arg);

        if (this.assembly.subtypeOf(argtype, this.typegen.noneType)) {
            return new SMTValue("true");
        }
        else if (!this.assembly.subtypeOf(this.typegen.noneType, argtype)) {
            return new SMTValue("false");
        }
        else if(this.typegen.typecheckAllKeys(argtype)) {
            return new SMTValue(`(= ${this.argToSMT(arg, this.typegen.keyType).emit()} bsqkey_none)`);
        }
        else {
            return new SMTValue(`(= ${this.argToSMT(arg, this.typegen.anyType).emit()} bsqterm_none)`);
        }
    }

    generateLoadConstTypedString(op: MIRLoadConstTypedString): SMTExp {
        const ttype = this.typegen.getMIRType(op.tkey);
        
        if (op.pfunckey === undefined) {
            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_stringof@cons "${this.typegen.mangleStringForSMT(op.tskey)}" ${op.ivalue})`));
        }
        else {
            const pfunc = (this.assembly.invokeDecls.get(op.pfunckey) || this.assembly.primitiveInvokeDecls.get(op.pfunckey)) as MIRInvokeDecl;

            const rval = new SMTValue(`(bsq_stringof@cons "${this.typegen.mangleStringForSMT(op.tskey)}" ${op.ivalue})`);
            const tv = this.generateTempName();
            const ivrtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(pfunc.resultType));
            const resulttype = this.typegen.getSMTTypeFor(this.currentRType);
        
            const ichk = new SMTLet(tv, new SMTValue(`(${this.invokenameToSMT(op.pfunckey)} ${op.ivalue})`));
            const checkerror = new SMTValue(`(is-result_error@${ivrtype} ${tv})`);
            const extracterror = (ivrtype !== resulttype) ? new SMTValue(`(result_error@${this.typegen.getSMTTypeFor(this.currentRType)} (result_error_code@${ivrtype} ${tv}))`) : new SMTValue(tv);

            if (this.typegen.assembly.subtypeOf(ttype, this.typegen.validatorType)) {
                const resultv = ichk.bind(new SMTValue(`(result_success_value@${ivrtype} ${tv})`));
                const cond = new SMTValue(`(or ${checkerror} (= ${resultv} false))`)
                return new SMTLet(this.varToSMTName(op.trgt), new SMTCond(cond, extracterror, rval))
            }
            else {
                const resultT = (this.typegen.assembly.conceptDecls.get(pfunc.resultType) as MIREntityTypeDecl).terms.get("T") as MIRType;
                const errtname = [...this.typegen.assembly.entityDecls].find((dcl) => dcl[0].startsWith("NSCore::Err<") && (dcl[1].terms.get("T") as MIRType).trkey === resultT.trkey) as [string, MIREntityTypeDecl];
                const successf = this.typegen.generateConstructorTest(errtname[0]);

                const resultv = ichk.bind(new SMTValue(`(result_success_value@${ivrtype} ${tv})`));
                const cond = new SMTValue(`(or ${checkerror} (${successf} ${resultv}))`)
                return new SMTLet(this.varToSMTName(op.trgt), new SMTCond(cond, extracterror, rval))
            }
        }
    }

    static expBodyTrivialCheck(bd: MIRBody): MIROp | undefined {
        if (bd.body.size !== 2 || (bd.body.get("entry") as MIRBasicBlock).ops.length !== 2) {
            return undefined;
        }

        const op = (bd.body.get("entry") as MIRBasicBlock).ops[0];
        if (op.tag === MIROpTag.MIRLoadConst) {
            return op;
        }
        else {
            return undefined;
        }
    }

    generateAccessConstantValue(cp: MIRAccessConstantValue): SMTExp {
        const cdecl = this.assembly.constantDecls.get(cp.ckey) as MIRConstantDecl;

        const top = SMTBodyEmitter.expBodyTrivialCheck(cdecl.value);
        if (top !== undefined) {
            const cvv = top as MIRLoadConst;
            return new SMTLet(this.varToSMTName(cp.trgt), this.generateConstantExp(cvv.src, this.getArgType(cvv.trgt)));
        }
        else {
            const tv = this.generateTempName();
            const ivrtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(cdecl.declaredType));
            const resulttype = this.typegen.getSMTTypeFor(this.currentRType);

            const constexp = new SMTValue(this.invokenameToSMT(cdecl.value.bkey));
            const checkerror = new SMTValue(`(is-result_error@${ivrtype} ${tv})`);
            const extracterror = (ivrtype !== resulttype) ? new SMTValue(`(result_error@${this.typegen.getSMTTypeFor(this.currentRType)} (result_error_code@${ivrtype} ${tv}))`) : new SMTValue(tv);
            const normalassign = new SMTLet(this.varToSMTName(cp.trgt), new SMTValue(`(result_success_value@${ivrtype} ${tv})`));

            return new SMTLet(tv, constexp, new SMTCond(checkerror, extracterror, normalassign));
        }
    }

    generateLoadFieldDefaultValue(ld: MIRLoadFieldDefaultValue): SMTExp {
        const fdecl = this.assembly.fieldDecls.get(ld.fkey) as MIRFieldDecl;

        const top = SMTBodyEmitter.expBodyTrivialCheck(fdecl.value as MIRBody);
        if (top !== undefined) {
            const cvv = top as MIRLoadConst;
            return new SMTLet(this.varToSMTName(ld.trgt), this.generateConstantExp(cvv.src, this.getArgType(cvv.trgt)));
        }
        else {
            const tv = this.generateTempName();
            const ivrtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(fdecl.declaredType));
            const resulttype = this.typegen.getSMTTypeFor(this.currentRType);

            const constexp = new SMTValue(this.invokenameToSMT((fdecl.value as MIRBody).bkey));
            const checkerror = new SMTValue(`(is-result_error@${ivrtype} ${tv})`);
            const extracterror = (ivrtype !== resulttype) ? new SMTValue(`(result_error@${resulttype} (result_error_code@${ivrtype} ${tv}))`) : new SMTValue(tv);
            const normalassign = new SMTLet(this.varToSMTName(ld.trgt), new SMTValue(`(result_success_value@${ivrtype} ${tv})`));

            return new SMTLet(tv, constexp, new SMTCond(checkerror, extracterror, normalassign));
        }
    }

    generateMIRConstructorPrimary(cp: MIRConstructorPrimary): SMTExp {
        const ctype = this.assembly.entityDecls.get(cp.tkey) as MIREntityTypeDecl;
        const fvals = cp.args.map((arg, i) => {
            const ftype = this.typegen.getMIRType(ctype.fields[i].declaredType);
            return this.argToSMT(arg, ftype).emit();
        });

        const smtctype = this.typegen.generateEntityConstructor(cp.tkey);
        const cexp = ctype.fields.length === 0 ? new SMTValue(smtctype) : new SMTValue(`(${smtctype} ${fvals.join(" ")})`);
        const bindexp = new SMTLet(this.varToSMTName(cp.trgt), cexp);
        if (ctype.invariants.length === 0) {
            return bindexp;
        }
        else {
            const testexp = new SMTValue(`(${this.typegen.mangleStringForSMT("invariant::" + cp.tkey)} ${this.varToSMTName(cp.trgt)})`);
            const resulttype = this.typegen.getSMTTypeFor(this.currentRType);
            const errexp = this.generateErrorCreate(cp.sinfo, resulttype);
            return bindexp.bind(new SMTCond(testexp, SMTFreeVar.generate(), errexp));
        }
    }

    generateMIRConstructorPrimaryCollectionEmpty(cpce: MIRConstructorPrimaryCollectionEmpty): SMTExp {
        const cpcetype = this.typegen.getMIRType(cpce.tkey);
        const smtctype = this.typegen.generateEntityConstructor(cpce.tkey);
        
        if(this.typegen.typecheckIsName(cpcetype, /NSCore::List<.*>/)) {
            return new SMTLet(this.varToSMTName(cpce.trgt), new SMTValue(`(${smtctype} 0 ${this.typegen.generateEmptyDataArrayFor(cpce.tkey)})`));
        }
        else if(this.typegen.typecheckIsName(cpcetype, /NSCore::Set<.*>/)) {
            return new SMTLet(this.varToSMTName(cpce.trgt), new SMTValue(`(${smtctype} 0 ${this.typegen.generateEmptyHasArrayFor(cpce.tkey)} ${this.typegen.generateEmptyDataArrayFor(cpce.tkey)} bsqterm_none)`));
        }
        else {
           return new SMTLet(this.varToSMTName(cpce.trgt), new SMTValue(`(${smtctype} 0 ${this.typegen.generateEmptyHasArrayFor(cpce.tkey)} ${this.typegen.generateEmptyKeyArrayFor(cpce.tkey)} ${this.typegen.generateEmptyDataArrayFor(cpce.tkey)} bsqterm_none)`));
        }
    }

    generateMIRConstructorPrimaryCollectionSingletons(cpcs: MIRConstructorPrimaryCollectionSingletons): SMTExp {
        const cpcstype = this.typegen.getMIRType(cpcs.tkey);
        const smtctype = this.typegen.generateEntityConstructor(cpcs.tkey);

        if(this.typegen.typecheckIsName(cpcstype, /NSCore::List<.*>/)) {
            const oftype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
            let consv = this.typegen.generateEmptyDataArrayFor(cpcs.tkey);
            for (let i = 0; i < cpcs.args.length; ++i) {
                consv = `(store ${consv} ${i} ${this.argToSMT(cpcs.args[i], oftype).emit()})`;
            }

            return new SMTLet(this.varToSMTName(cpcs.trgt), new SMTValue(`(${smtctype} ${cpcs.args.length} ${consv})`));
        }
        else if(this.typegen.typecheckIsName(cpcstype, /NSCore::Set<.*>/)) {
            const oftype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("T") as MIRType;

            const realkeytype = this.typegen.getKeyProjectedTypeFrom(oftype);
            const kltype = [...this.typegen.assembly.entityDecls].find((edecl) => edecl[1].ns === "NSCore" && edecl[1].name === "KeyList" && (edecl[1].terms.get("K") as MIRType).trkey === realkeytype.trkey) as [string, MIREntityTypeDecl];
            const klcons = this.typegen.generateEntityConstructor(kltype[1].tkey);

            let consv = `(${smtctype} %CTR% %HAS% %DATA% %KL%)`;
            for (let i = cpcs.args.length - 1; i >= 1; --i) {
                const arg = cpcs.args[i];

                const key = this.typegen.getKeyFrom(this.argToSMT(arg, oftype).emit(), oftype);
                const ctrvar = this.generateTempName();
                const ctrup = `(ite (select %HAS% ${key}) %CTR% (+ %CTR% 1))`;

                const hasvar = this.generateTempName();
                const hasup = `(store %HAS% ${key} true)`;

                const datavar = this.generateTempName();
                const dataup = `(store %DATA% ${key} ${this.argToSMT(arg, oftype).emit()})`;

                const keyvar = this.generateTempName();
                const keyup = `(ite (select %HAS% ${key}) %KEY% (${klcons} ${key} %KEY%))`;

                const body = consv.replace(/%CTR%/g, ctrvar).replace(/%HAS%/g, hasvar).replace(/%DATA%/g, datavar).replace(/%KEY%/g, keyvar);
                consv = `(let ((${ctrvar} ${ctrup}) (${hasvar} ${hasup}) (${datavar} ${dataup}) (${keyvar} ${keyup})) ${body})`
            }
            const key = this.typegen.getKeyFrom(this.argToSMT(cpcs.args[0], oftype).emit(), oftype);
            const val = this.argToSMT(cpcs.args[0], oftype).emit();
            const final = consv
                .replace(/%CTR%/g, "1")
                .replace(/%HAS%/g, `(store ${this.typegen.generateEmptyHasArrayFor(cpcs.tkey)} ${key} true)`)
                .replace(/%DATA%/g, `(store ${this.typegen.generateEmptyDataArrayFor(cpcs.tkey)} ${key} ${val})`)
                .replace(/%KEY%/g, `(${klcons} ${key} bsqterm_none)`);

            return new SMTLet(this.varToSMTName(cpcs.trgt), new SMTValue(final));
        }
        else {
            const ktype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("K") as MIRType;
            const vtype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("V") as MIRType;
            const realkeytype = this.typegen.getKeyProjectedTypeFrom(ktype);

            const entrytype = [...this.typegen.assembly.entityDecls].find((edecl) => edecl[1].ns === "NSCore" && edecl[1].name === "MapEntry" && (edecl[1].terms.get("K") as MIRType).trkey === ktype.trkey && (edecl[1].terms.get("V") as MIRType).trkey === vtype.trkey) as [string, MIREntityTypeDecl];
            const entrykey = this.typegen.generateEntityAccessor(entrytype[1].tkey, (entrytype[1].fields.find((fd) => fd.name === "key") as MIRFieldDecl).fkey);
            const entryvalue = this.typegen.generateEntityAccessor(entrytype[1].tkey, (entrytype[1].fields.find((fd) => fd.name === "value") as MIRFieldDecl).fkey);

            const kltype = [...this.typegen.assembly.entityDecls].find((edecl) => edecl[1].ns === "NSCore" && edecl[1].name === "KeyList" && (edecl[1].terms.get("K") as MIRType).trkey === realkeytype.trkey) as [string, MIREntityTypeDecl];
            const klcons = this.typegen.generateEntityConstructor(kltype[1].tkey);

            let consv = `(${smtctype} %CTR% %HAS% %ENTRYKEY% %ENTRYDATA% %KL%)`;
            for (let i = cpcs.args.length - 1; i >= 1; --i) {
                const arg = cpcs.args[i];
                const entrykeyexp = `(${entrykey}, ${this.argToSMT(arg, this.typegen.getMIRType(entrytype[1].tkey)).emit()})`;
                const entryvalexp = `(${entryvalue}, ${this.argToSMT(arg, this.typegen.getMIRType(entrytype[1].tkey)).emit()})`;

                const key = this.typegen.getKeyFrom(entrykeyexp, ktype);
                const ctrvar = this.generateTempName();
                const ctrup = `(ite (select %HAS% ${key}) %CTR% (+ %CTR% 1))`;

                const hasvar = this.generateTempName();
                const hasup = `(store %HAS% ${key} true)`;

                const entrykeyvar = this.generateTempName();
                const entrykeyup = `(store %ENTRYKEY% ${key} ${entrykeyexp})`;

                const entrydatavar = this.generateTempName();
                const entrydataup = `(store %ENTRYDATA% ${key} ${entryvalexp})`;

                const keyvar = this.generateTempName();
                const keyup = `(ite (select %HAS% ${key}) %KEY% (${klcons} ${key} %KEY%))`;

                const body = consv.replace(/%CTR%/g, ctrvar).replace(/%HAS%/g, hasvar).replace(/%ENTRYKEY%/g, entrykeyvar).replace(/%ENTRYDATA%/g, entrydatavar).replace(/%KEY%/g, keyvar);
                consv = `(let ((${ctrvar} ${ctrup}) (${hasvar} ${hasup}) (${entrykeyvar} ${entrykeyup}) (${entrydatavar} ${entrydataup})  (${keyvar} ${keyup})) ${body})`
            }
            const entrykeyexp0 = `(${entrykey}, ${this.argToSMT(cpcs.args[0], this.typegen.getMIRType(entrytype[1].tkey)).emit()})`;
            const entryvalexp0 = `(${entryvalue}, ${this.argToSMT(cpcs.args[0], this.typegen.getMIRType(entrytype[1].tkey)).emit()})`;

            const key = this.typegen.getKeyFrom(entrykeyexp0, ktype);
            const final = consv
                .replace(/%CTR%/g, "1")
                .replace(/%HAS%/g, `(store ${this.typegen.generateEmptyHasArrayFor(cpcs.tkey)} ${key} true)`)
                .replace(/%ENTRYKEY%/g, `(store ${this.typegen.generateEmptyKeyArrayFor(cpcs.tkey)} ${key} ${entrykeyexp0})`)
                .replace(/%ENTRYKEY%/g, `(store ${this.typegen.generateEmptyDataArrayFor(cpcs.tkey)} ${key} ${entryvalexp0})`)
                .replace(/%KEY%/g, `(${klcons} ${key} bsqterm_none)`);

            return new SMTLet(this.varToSMTName(cpcs.trgt), new SMTValue(final));
        }
    }

    generateMIRConstructorTuple(op: MIRConstructorTuple): SMTExp {
        let cvals = "bsqtuple_array_empty";
        for (let i = 0; i < op.args.length; ++i) {
            cvals = `(store ${cvals} ${i} ${this.argToSMT(op.args[i], this.typegen.anyType)})`;
        }

        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_tuple@cons ${cvals})`));
    }

    generateMIRConstructorRecord(op: MIRConstructorRecord): SMTExp {
        let cvals = "bsqrecord_array_empty";
        for (let i = 0; i < op.args.length; ++i) {
            cvals = `(store ${cvals} "${op.args[i][0]}" ${this.argToSMT(op.args[i][1], this.typegen.anyType)})`;
        }

        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_record@cons ${cvals})`));
    }

    generateMIRConstructorEphemeralValueList(op: MIRConstructorEphemeralValueList): SMTExp {
        const etype = this.typegen.getMIRType(op.resultEphemeralListType).options[0] as MIREpemeralListType;

        let args: string[] = [];
        for(let i = 0; i < op.args.length; ++i) {
            args.push(this.argToSMT(op.args[i], etype.entries[i]).emit());
        } 

        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(${this.typegen.generateEntityConstructor(etype.trkey)} ${args.join(" ")})`));
    }

    generateMIRAccessFromIndexExpression(arg: MIRArgument, idx: number, resultAccessType: MIRType): SMTExp {
        const tuptype = this.getArgType(arg);
        const hasidx = this.typegen.tupleHasIndex(tuptype, idx);
    
        if(hasidx === "no") {
            return this.typegen.coerce(new SMTValue("bsqkey_none"), this.typegen.noneType, resultAccessType);
        }
        else {
            const tupcontents = this.typegen.typecheckTuple(tuptype) ? `(bsq_tuple_entries ${this.varToSMTName(arg)})` : `(bsq_tuple_entries (bsqterm_tuple_value ${this.varToSMTName(arg)}))`;
            const select = new SMTValue(`(select ${tupcontents} ${idx})`);
            if(hasidx === "yes") {
                return this.typegen.coerce(select, this.typegen.anyType, resultAccessType);
            }
            else {
                const getop = new SMTCond(new SMTValue(`(= ${select.emit()} bsqterm@clear)`), new SMTValue("bsqterm_none"), select); 
                return this.typegen.coerce(getop, this.typegen.anyType, resultAccessType);
            }
        }
    }

    generateMIRProjectFromIndecies(op: MIRProjectFromIndecies, resultAccessType: MIRType): SMTExp { 
        const intotypes = this.typegen.typecheckEphemeral(resultAccessType) ? (resultAccessType.options[0] as MIREpemeralListType).entries : [];
        let vals: string[] = [];

        for (let i = 0; i < op.indecies.length; ++i) {
            vals.push(this.generateMIRAccessFromIndexExpression(op.arg, op.indecies[i], intotypes[i] || this.typegen.anyType).emit());
        }

        if (this.typegen.typecheckEphemeral(resultAccessType)) {
            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(${this.typegen.generateEntityConstructor(resultAccessType.trkey)} ${vals.join(" ")})`));
        }
        else {
            let cvals = "bsqtuple_array_empty";
            for (let i = 0; i < vals.length; ++i) {
                cvals = `(store ${cvals} ${i} ${vals[i]})`;
            }

            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_tuple@cons ${cvals})`));
        }
    }
    
    generateMIRModifyWithIndecies(op: MIRModifyWithIndecies, resultTupleType: MIRType): SMTExp {
        const updmax = Math.max(...op.updates.map((upd) => upd[0] + 1));

        let cvals = "bsqtuple_array_empty";
        for (let i = 0; i < updmax; ++i) {
            const upd = op.updates.find((update) => update[0] === i);
            if (upd !== undefined) {
                cvals = `(store ${cvals} ${i} ${this.argToSMT(upd[1], this.typegen.anyType)})`;
            }
            else {
                cvals = `(store ${cvals} ${i} ${this.generateMIRAccessFromIndexExpression(op.arg, i, this.typegen.anyType).emit()})`;
            }
        }

        const rmax = this.typegen.getMaxTupleLength(resultTupleType);
        let tc = this.typegen.typecheckTuple(this.getArgType(op.arg)) ? `(bsq_tuple_entries ${this.varToSMTName(op.arg)})` : `(bsq_tuple_entries (bsqterm_tuple_value ${this.varToSMTName(op.arg)}))`;
        for (let i = updmax; i < rmax; ++i) {
            cvals = `(store ${cvals} ${i} (select ${tc} ${i}))`;
        }

        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_tuple@cons ${cvals})`));
    }

    generateMIRStructuredExtendTuple(op: MIRStructuredExtendTuple, resultTupleType: MIRType): SMTExp {
        //this is the exact number of indecies in arg -- see typecheck
        const btuple = this.typegen.getMaxTupleLength(this.typegen.getMIRType(op.argInferType));
        const ftuple = this.typegen.getMaxTupleLength(resultTupleType);

        let cvals = this.typegen.typecheckTuple(this.getArgType(op.arg)) ? `(bsq_tuple_entries ${this.varToSMTName(op.arg)})` : `(bsq_tuple_entries (bsqterm_tuple_value ${this.varToSMTName(op.arg)}))`;
        let mvals = this.typegen.typecheckTuple(this.getArgType(op.update)) ? `(bsq_tuple_entries ${this.varToSMTName(op.update)})` : `(bsq_tuple_entries (bsqterm_tuple_value ${this.varToSMTName(op.update)}))`;
           
        for (let i = 0; i < ftuple; ++i) {
            cvals = `(store ${cvals} ${btuple + i} (select ${mvals} ${i}))`;
        }

        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_tuple@cons ${cvals})`));
    }

    generateMIRAccessFromPropertyExpression(arg: MIRArgument, property: string, resultAccessType: MIRType): SMTExp {
        const rectype = this.getArgType(arg);
        const hasproperty = this.typegen.recordHasField(rectype, property);
    
        if(hasproperty === "no") {
            return this.typegen.coerce(new SMTValue("bsqkey_none"), this.typegen.noneType, resultAccessType);
        }
        else {
            const reccontents = this.typegen.typecheckRecord(rectype) ? `(bsq_record_entries ${this.varToSMTName(arg)})` : `(bsq_record_entries (bsqterm_record_value ${this.varToSMTName(arg)}))`;
            const select = new SMTValue(`(select ${reccontents} ${property})`);
            if(hasproperty === "yes") {
                return this.typegen.coerce(select, this.typegen.anyType, resultAccessType);
            }
            else {
                const getop = new SMTCond(new SMTValue(`(= ${select.emit()} bsqterm@clear)`), new SMTValue("bsqterm_none"), select); 
                return this.typegen.coerce(getop, this.typegen.anyType, resultAccessType);
            }
        }
    }

    generateMIRProjectFromProperties(op: MIRProjectFromProperties, resultAccessType: MIRType): SMTExp {
        const intotypes = this.typegen.typecheckEphemeral(resultAccessType) ? (resultAccessType.options[0] as MIREpemeralListType).entries : [];
        let vals: string[] = [];

        for (let i = 0; i < op.properties.length; ++i) {
            vals.push(this.generateMIRAccessFromPropertyExpression(op.arg, op.properties[i], intotypes[i] || this.typegen.anyType).emit());
        }

        if (this.typegen.typecheckEphemeral(resultAccessType)) {
            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(${this.typegen.generateEntityConstructor(resultAccessType.trkey)} ${vals.join(" ")})`));
        }
        else {
            let cvals = "bsqrecord_array_empty";
            for (let i = 0; i < vals.length; ++i) {
                cvals = `(store ${cvals} "${op.properties[i]}" ${vals[i]})`;
            }

            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_record@cons ${cvals})`));
        }
    }

    generateMIRModifyWithProperties(op: MIRModifyWithProperties, resultRecordType: MIRType): SMTExp {
        const pmax = this.typegen.getMaxPropertySet(resultRecordType);

        let cvals = this.typegen.typecheckRecord(this.getArgType(op.arg)) ? `(bsq_record_entries ${this.varToSMTName(op.arg)})` : `(bsq_record_entries (bsqterm_record_value ${this.varToSMTName(op.arg)}))`;
        for (let i = 0; i < pmax.length; ++i) {
            const pname = pmax[i];
            const upd = op.updates.find((update) => update[0] === pname);
            if (upd !== undefined) {
                cvals = `(store ${cvals} "${pname}" ${this.argToSMT(upd[1], this.typegen.anyType)})`;
            }
        }

        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_record@cons ${cvals})`));
    }

    generateMIRStructuredExtendRecord(op: MIRStructuredExtendRecord, resultRecordType: MIRType): SMTExp {
        const argvals = this.typegen.typecheckRecord(this.getArgType(op.arg)) ? `(bsq_record_entries ${this.varToSMTName(op.arg)})` : `(bsq_record_entries (bsqterm_record_value ${this.varToSMTName(op.arg)}))`;
        let cvals = argvals;

        const rprops = this.typegen.getMaxPropertySet(resultRecordType);
        const mtype = this.typegen.getMIRType(op.updateInferType);
        for(let i = 0; i < rprops.length; ++i) {
            const pname = rprops[i];
            const uhas = this.typegen.recordHasField(mtype, pname);
            if(uhas === "no") {
                //nothing to do
            }
            else if (uhas === "yes") {
                cvals = `(store ${cvals} "${pname}" ${this.generateMIRAccessFromPropertyExpression(op.update, pname, this.typegen.anyType)})`
            }
            else {
                let mvals = this.typegen.typecheckRecord(this.getArgType(op.update)) ? `(bsq_record_entries ${this.varToSMTName(op.update)})` : `(bsq_record_entries (bsqterm_record_value ${this.varToSMTName(op.update)}))`;
        
                const check = new SMTValue(`(= (select ${mvals} "${pname}") bsqterm@clear)`);
                const caccess = new SMTCond(check, new SMTValue(`(select ${argvals} "${pname}")`), new SMTValue(`(select ${mvals} "${pname}")`));

                cvals =  `(store ${cvals} "${pname}" ${caccess})`;
            }
        }

        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_record@cons ${cvals})`));
    }

    generateVFieldLookup(arg: MIRArgument, infertype: MIRType, fdecl: MIRFieldDecl): SMTExp {
        const lname = `resolve_${fdecl.fkey}_from_${infertype.trkey}`;
        let decl = this.vfieldLookups.find((lookup) => lookup.lname === lname);
        if(decl === undefined) {
            this.vfieldLookups.push({ arg: arg, infertype: infertype, fdecl: fdecl, lname: lname });
        }

        return new SMTValue(`(${this.typegen.mangleStringForSMT(lname)} ${this.argToSMT(arg, infertype)})`);
    }

    generateMIRAccessFromField(op: MIRAccessFromField, resultAccessType: MIRType): SMTExp {
        const inferargtype = this.typegen.getMIRType(op.argInferType);
        const fdecl = this.assembly.fieldDecls.get(op.field) as MIRFieldDecl;
        const ftype = this.typegen.getMIRType(fdecl.declaredType);

        if (this.typegen.typecheckUEntity(inferargtype)) {
            const access = new SMTValue(`(${this.typegen.generateEntityAccessor(this.typegen.getEntityEKey(inferargtype), op.field)} ${this.argToSMT(op.arg, inferargtype).emit()})`);
            return new SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(access, ftype, resultAccessType));
        }
        else {
            const access = this.generateVFieldLookup(op.arg, inferargtype, fdecl);
            return new SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(access, ftype, resultAccessType));
        }
    }

    generateVFieldProject(arg: MIRArgument, infertype: MIRType, fdecls: MIRFieldDecl[]): SMTExp {
        const pname = `project_${fdecls.map((fd) => fd.fkey).sort().join("*")}_from_${infertype.trkey}`;
        let decl = this.vfieldProjects.find((lookup) => lookup.pname === pname);
        if(decl === undefined) {
            this.vfieldProjects.push({ arg: arg, infertype: infertype, fdecls: fdecls, pname: pname });
        }

        return new SMTValue(`(${this.typegen.mangleStringForSMT(pname)} ${this.argToSMT(arg, infertype)})`);
    }

    generateMIRProjectFromFields(op: MIRProjectFromFields): SMTExp {
        const inferargtype = this.typegen.getMIRType(op.argInferType);
        
        if (this.typegen.typecheckUEntity(inferargtype)) {
            let cvals = "bsqrecord_array_empty";
            for (let i = 0; i < op.fields.length; ++i) {
                const fdecl = this.assembly.fieldDecls.get(op.fields[i]) as MIRFieldDecl;
                const ftype = this.typegen.getMIRType(fdecl.declaredType);

                const access = new SMTValue(`(${this.typegen.generateEntityAccessor(this.typegen.getEntityEKey(inferargtype), op.fields[i])} ${this.argToSMT(op.arg, inferargtype).emit()})`);
                cvals = `(store ${cvals} "${fdecl.name}" ${this.typegen.coerce(access, ftype, this.typegen.anyType)})`;
            }

            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(bsq_record@cons ${cvals})`));
        }
        else {
            const access = this.generateVFieldProject(op.arg, inferargtype, op.fields.map((f) => this.assembly.fieldDecls.get(f) as MIRFieldDecl));
            return new SMTLet(this.varToSMTName(op.trgt), access);
        }
    }

    generateVFieldUpdates(arg: MIRArgument, infertype: MIRType, fupds: [MIRFieldDecl, MIRArgument][]): SMTExp {
        const upnames = fupds.map((fud) => `${fud[0].fkey}->${this.getArgType(fud[1])}`);
        const uname = `update_${upnames.sort().join("*")}_in_${infertype.trkey}`;
        let decl = this.vfieldUpdates.find((lookup) => lookup.uname === uname);
        if(decl === undefined) {
            this.vfieldUpdates.push({ arg: arg, infertype: infertype, fupds: fupds, uname: uname });
        }

        return new SMTValue(`(${this.typegen.mangleStringForSMT(uname)} ${this.argToSMT(arg, infertype)} ${fupds.map((upd) => this.argToSMT(upd[1], this.getArgType(upd[1])).emit()).join(" ")})`);
    }

    generateMIRModifyWithFields(op: MIRModifyWithFields): SMTExp {
        const inferargtype = this.typegen.getMIRType(op.argInferType);
        
        if (this.typegen.typecheckUEntity(inferargtype)) {
            const ekey = this.typegen.getEntityEKey(inferargtype);
            const utype = this.typegen.assembly.entityDecls.get(ekey) as MIREntityTypeDecl;
            let cvals: string[] = [];
            for (let i = 0; i < utype.fields.length; ++i) {
                const fdecl = utype.fields[i];
                const ftype = this.typegen.getMIRType(fdecl.declaredType);

                const upd = op.updates.find((update) => update[0] == fdecl.fkey);
                if(upd !== undefined) {
                    cvals.push(this.argToSMT(upd[1], ftype).emit());
                }
                else {
                    cvals.push(`(${this.typegen.generateEntityAccessor(ekey, fdecl.fkey)} ${this.argToSMT(op.arg, inferargtype).emit()})`);
                }
            }

            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(${this.typegen.generateEntityConstructor(ekey)} ${cvals.join(" ")})`));
        }
        else {
            const access = this.generateVFieldUpdates(op.arg, inferargtype, op.updates.map((upd) => [this.assembly.fieldDecls.get(upd[0]) as MIRFieldDecl, upd[1]]));
            return new SMTLet(this.varToSMTName(op.trgt), access);
        }
    }
    
    generateVFieldExtend(arg: MIRArgument, infertype: MIRType, merge: MIRArgument, infermerge: MIRType, fieldResolves: [string, MIRFieldDecl][]): SMTExp {
        const upnames = fieldResolves.map((fr) => `${fr[0]}->${fr[1].fkey}`);
        const mname = `merge_${infertype.trkey}_${upnames.join("*")}_with_${infermerge.trkey}`;
        let decl = this.vobjmerges.find((lookup) => lookup.mname === mname);
        if(decl === undefined) {
            this.vobjmerges.push({ arg: arg, infertype: infertype, merge: merge, infermergetype: infermerge, fieldResolves: fieldResolves, mname: mname });
        }

        return new SMTValue(`(${this.typegen.mangleStringForSMT(mname)} ${this.argToSMT(arg, infertype)} ${this.argToSMT(merge, infermerge)})`);
    }

    generateMIRStructuredExtendObject(op: MIRStructuredExtendObject): SMTExp {
        const inferargtype = this.typegen.getMIRType(op.argInferType);
        const mergeargtype = this.typegen.getMIRType(op.updateInferType);
        
        if (this.typegen.typecheckUEntity(inferargtype)) {
            const ekey = this.typegen.getEntityEKey(inferargtype);
            const utype = this.typegen.assembly.entityDecls.get(ekey) as MIREntityTypeDecl;
            let cvals: string[] = [];
            for (let i = 0; i < utype.fields.length; ++i) {
                const fdecl = utype.fields[i];
                const ftype = this.typegen.getMIRType(fdecl.declaredType);

                const fp = op.fieldResolves.find((tfp) => tfp[1] === fdecl.fkey);
                const faccess = `(${this.typegen.generateEntityAccessor(ekey, fdecl.fkey)} ${this.argToSMT(op.arg, inferargtype).emit()})`;
                if(fp === undefined) {
                    cvals.push(faccess);
                }
                else {
                    const hasp = this.typegen.recordHasField(mergeargtype, fp[0]);
                    if(hasp === "no") {
                        cvals.push(faccess);
                    }
                    else if (hasp === "yes") {
                        cvals.push(this.generateMIRAccessFromPropertyExpression(op.arg, fp[0], ftype).emit());
                    }
                    else {
                        let mvals = this.typegen.typecheckRecord(this.getArgType(op.update)) ? `(bsq_record_entries ${this.varToSMTName(op.update)})` : `(bsq_record_entries (bsqterm_record_value ${this.varToSMTName(op.update)}))`;
                        const check = new SMTValue(`(= (select ${mvals} "${fp[0]}") bsqterm@clear)`);

                        cvals.push(new SMTCond(check, new SMTValue(faccess), new SMTValue(`(select ${mvals} "${fp[0]}")`)).emit());
                    }
                }
            }

            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(${this.typegen.generateEntityConstructor(ekey)} ${cvals.join(" ")})`));
        }
        else {
            const access = this.generateVFieldExtend(op.arg, inferargtype, op.update, mergeargtype, op.fieldResolves.map((fr) => [fr[0], this.assembly.fieldDecls.get(fr[1]) as MIRFieldDecl]));
            return new SMTLet(this.varToSMTName(op.trgt), access);
        }
    }

    generateMIRInvokeFixedFunction(ivop: MIRInvokeFixedFunction, gas: number | undefined): SMTExp {
        let vals: string[] = [];
        const idecl = (this.assembly.invokeDecls.get(ivop.mkey) || this.assembly.primitiveInvokeDecls.get(ivop.mkey)) as MIRInvokeDecl;

        for (let i = 0; i < ivop.args.length; ++i) {
            vals.push(this.argToSMT(ivop.args[i], this.assembly.typeMap.get(idecl.params[i].type) as MIRType).emit());
        }

        const tv = this.generateTempName();
        const ivrtype = this.typegen.typeToSMTCategory(this.typegen.getMIRType((idecl as MIRInvokeDecl).resultType));
        const resulttype = this.typegen.typeToSMTCategory(this.currentRType);

        const checkerror = new SMTValue(`(is-result_error@${ivrtype} ${tv})`);
        const extracterror = (ivrtype !== resulttype) ? new SMTValue(`(result_error@${resulttype} (result_error_code@${ivrtype} ${tv}))`) : new SMTValue(tv);
        const normalassign = new SMTLet(this.varToSMTName(ivop.trgt), new SMTValue(`(result_success_value@${ivrtype} ${tv})`));

        if (this.currentSCC === undefined || !this.currentSCC.has(ivop.mkey)) {
            const invokeexp = new SMTValue(vals.length !== 0 ? `(${this.invokenameToSMT(ivop.mkey)} ${vals.join(" ")})` : this.invokenameToSMT(ivop.mkey));
            return new SMTLet(tv, invokeexp, new SMTCond(checkerror, extracterror, normalassign));
        }
        else {
            if (gas === 0) {
                const invokeexp = this.generateBMCLimitCreate(ivop.mkey, ivrtype);
                return new SMTLet(tv, invokeexp, new SMTCond(checkerror, extracterror, normalassign));
            }
            else {
                const invokeexp = new SMTValue(vals.length !== 0 ? `(${this.invokenameToSMT(ivop.mkey)}@gas${gas} ${vals.join(" ")})` : this.invokenameToSMT(ivop.mkey));
                return new SMTLet(tv, invokeexp, new SMTCond(checkerror, extracterror, normalassign));
            }
        }
    }

    generateEquals(op: string, lhsinfertype: MIRType, lhs: MIRArgument, rhsinfertype: MIRType, rhs: MIRArgument): string {
        const lhsargtype = this.getArgType(lhs);
        const rhsargtype = this.getArgType(rhs);

        let coreop = "";
        if (lhsinfertype.trkey === "NSCore::Bool" && rhsinfertype.trkey === "NSCore::Bool") {
            const lhsbool = (lhsargtype.trkey === "NSCore::Bool") ? this.argToSMT(lhs, lhsargtype).emit() : this.argToSMT(lhs, lhsinfertype).emit();
            const rhsbool = (rhsargtype.trkey === "NSCore::Bool") ? this.argToSMT(rhs, rhsargtype).emit() : this.argToSMT(rhs, rhsinfertype).emit();
            coreop = `(= ${lhsbool} ${rhsbool})`;
        }
        else if (lhsinfertype.trkey === "NSCore::Int" && rhsinfertype.trkey === "NSCore::Int") {
            const lhsint = (lhsargtype.trkey === "NSCore::Int") ? this.argToSMT(lhs, lhsargtype).emit() : this.argToSMT(lhs, lhsinfertype).emit();
            const rhsint = (rhsargtype.trkey === "NSCore::Int") ? this.argToSMT(rhs, rhsargtype).emit() : this.argToSMT(rhs, rhsinfertype).emit();
            coreop = `(= ${lhsint} ${rhsint})`;
        }
        else if (lhsinfertype.trkey === "NSCore::String" && rhsinfertype.trkey === "NSCore::String") {
            const lhsstring = (lhsargtype.trkey === "NSCore::String") ? this.argToSMT(lhs, lhsargtype).emit() : this.argToSMT(lhs, lhsinfertype).emit();
            const rhsstring = (rhsargtype.trkey === "NSCore::String") ? this.argToSMT(rhs, rhsargtype).emit() : this.argToSMT(rhs, rhsinfertype).emit();
            coreop = `(= ${lhsstring} ${rhsstring})`;
        }
        else if(lhsargtype.trkey === rhsargtype.trkey) {
            coreop = `(= ${this.argToSMT(lhs, lhsargtype).emit()} ${this.argToSMT(rhs, rhsargtype).emit()})`;
        }
        else {
            coreop = `(= ${this.argToSMT(lhs, this.typegen.keyType).emit()} ${this.argToSMT(rhs, this.typegen.keyType).emit()})`;
        }

        return op === "!=" ? `(not ${coreop})` : coreop;
    }

    generateCompare(op: string, lhsinfertype: MIRType, lhs: MIRArgument, rhsinfertype: MIRType, rhs: MIRArgument): string {
        const lhsargtype = this.getArgType(lhs);
        const rhsargtype = this.getArgType(rhs);

        const lhsint = (lhsargtype.trkey === "NSCore::Int") ? this.argToSMT(lhs, lhsargtype).emit() : this.argToSMT(lhs, lhsinfertype).emit();
        const rhsint = (rhsargtype.trkey === "NSCore::Int") ? this.argToSMT(rhs, rhsargtype).emit() : this.argToSMT(rhs, rhsinfertype).emit();
        return `(${op} ${lhsint} ${rhsint})`;
    }

    generateSubtypeTupleCheck(argv: string, argt: string, accessor_macro: string, nothas_macro: string, argtype: MIRType, oftype: MIRTupleType, gas: number): string {
        const subtypesig = `subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)}@gas${gas} ((atuple ${argt})) Bool`;

        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;

            let reqlen = oftype.entries.findIndex((entry) => entry.isOptional);
            if (reqlen === -1) {
                reqlen = oftype.entries.length;
            }

            let checks: string[] = [];
            const maxlength = this.typegen.isTupleType(argtype) ? SMTTypeEmitter.getTupleTypeMaxLength(argtype) : -1;

            if (maxlength !== -1) {
                checks.push(`(not (< ${maxlength} ${reqlen}))`);
            }

            for (let i = 0; i < oftype.entries.length; ++i) {
                if (!oftype.entries[i].isOptional) {
                    if (!(this.typegen.isKnownLayoutTupleType(argtype) && this.typegen.assembly.subtypeOf(SMTTypeEmitter.getKnownLayoutTupleType(argtype).entries[i].type, oftype.entries[i].type))) {
                        checks.push(this.generateTypeCheck(`${accessor_macro.replace("ARG", "atuple").replace("IDX", i.toString())}`, this.typegen.anyType, oftype.entries[i].type, true, gas - 1));
                    }
                }
                else {
                    if (maxlength <= i) {
                        const chk = this.generateTypeCheck(`${accessor_macro.replace("ARG", "atuple").replace("IDX", i.toString())}`, this.typegen.anyType, oftype.entries[i].type, true, gas - 1);
                        checks.push(`(or ${nothas_macro.replace("ARG", "atuple").replace("IDX", i.toString())} ${chk})`);
                    }
                }
            }

            if(maxlength === -1) {
                let nv = "bsqtuple_array_empty";
                for (let i = 0; i < oftype.entries.length; ++i) {
                    nv = `(store ${nv} ${i} (select (bsqterm_tuple_entries atuple) ${i}))`;
                }
                checks.push(`(= ${nv} (bsqterm_tuple_entries atuple))`);
            }
            else {
                if (maxlength > oftype.entries.length) {
                    for (let i = oftype.entries.length; i < maxlength; ++i) {
                        checks.push(nothas_macro.replace("ARG", "atuple").replace("IDX", i.toString()));
                    }
                }
            }

            let op = "";
            if (checks.includes("false")) {
                op = "false";
            }
            else {
                checks = checks.filter((chk) => chk !== "true");
                if(checks.length === 0) {
                    op = "true";
                }
                else if(checks.length === 1) {
                    op = checks[0];
                }
                else {
                    op = `(and ${checks.join(" ")})`;
                }
            }

            const decl = "(define-fun " + subtypesig
            + "\n  " + op
            + ")\n"; 

            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }

        return `(subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)}@gas${gas} ${argv})`;
    }

    generateSubtypeRecordCheck(argv: string, argt: string, accessor_macro: string, nothas_macro: string, argtype: MIRType, oftype: MIRRecordType, gas: number): string {
        const subtypesig = `subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)}@gas${gas} ((arecord ${argt})) Bool`;

        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;

            let checks: string[] = [];
            for (let i = 0; i < oftype.entries.length; ++i) {
                const pname = oftype.entries[i].name;
                if (!oftype.entries[i].isOptional) {
                    if (!(this.typegen.isKnownLayoutRecordType(argtype) && this.typegen.assembly.subtypeOf((SMTTypeEmitter.getKnownLayoutRecordType(argtype).entries.find((e) => e.name === pname) as MIRRecordTypeEntry).type, oftype.entries[i].type))) {
                        checks.push(this.generateTypeCheck(`${accessor_macro.replace("ARG", "arecord").replace("PNAME", pname)}`, this.typegen.anyType, oftype.entries[i].type, true, gas - 1));
                    }
                }
                else {
                    if (!this.typegen.isRecordType(argtype) || SMTTypeEmitter.getRecordTypeMaxPropertySet(argtype).includes(pname)) {
                        const chk = this.generateTypeCheck(`${accessor_macro.replace("ARG", "arecord").replace("PNAME", pname)}`, this.typegen.anyType, oftype.entries[i].type, true, gas - 1);
                        checks.push(`(or ${nothas_macro.replace("ARG", "arecord").replace("PNAME", pname)} ${chk})`);
                    }
                }
            }

            if (this.typegen.isRecordType(argtype)) {
                const possibleargproperties = SMTTypeEmitter.getRecordTypeMaxPropertySet(argtype);
                for (let i = 0; i < possibleargproperties.length; ++i) {
                    const pname = possibleargproperties[i];
                    if (oftype.entries.find((p) => p.name === pname) === undefined) {
                        checks.push(nothas_macro.replace("ARG", "arecord").replace("PNAME", pname));
                    }
                }
            }
            else {
                let nv = "bsqrecord_array_empty";
                for(let i = 0; i < oftype.entries.length; ++i) {
                    const pname = oftype.entries[i].name;
                    nv = `(store ${nv} "${pname}" (select (bsqterm_record_entries arecord) "${pname}"))`;
                }
                checks.push(`(= ${nv} (bsqterm_record_entries arecord))`);
            }

            let op = "";
            if (checks.includes("false")) {
                op = "false";
            }
            else {
                checks = checks.filter((chk) => chk !== "true");
                if(checks.length === 0) {
                    op = "true";
                }
                else if(checks.length === 1) {
                    op = checks[0];
                }
                else {
                    op = `(and ${checks.join(" ")})`;
                }
            }

            const decl = "(define-fun " + subtypesig
            + "\n  " + op
            + ")\n"; 

            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }

        return `(subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)}@gas${gas} ${argv})`;
    }

    generateFastTupleTypeCheck(arg: string, argtype: MIRType, oftype: MIRTupleType, inline: boolean, gas: number): string {
        if(this.typegen.isSimpleBoolType(argtype) || this.typegen.isSimpleIntType(argtype) || this.typegen.isSimpleStringType(argtype) || this.typegen.isKeyType(argtype)) {
            return "false";
        }
        if (this.typegen.isTupleType(argtype)) {
            if (this.typegen.isKnownLayoutTupleType(argtype)) {
                const atuple = SMTTypeEmitter.getKnownLayoutTupleType(argtype);
                if(oftype.entries.length < atuple.entries.length) {
                    return "false";
                }
                else if(oftype.entries.length > atuple.entries.length && !oftype.entries[atuple.entries.length].isOptional) {
                    return "false";
                }
                else {
                    if (inline) {
                        let ttests = atuple.entries.map((entry, i) => this.generateTypeCheck(`(${this.typegen.generateTupleAccessor(argtype, i)} ${arg})`, this.typegen.anyType, entry.type, false, gas));

                        if (ttests.includes("false")) {
                            return "false";
                        }
                        else {
                            ttests = ttests.filter((chk) => chk !== "true");
                            if(ttests.length === 0) {
                                return "true";
                            }
                            else if(ttests.length === 1) {
                                return ttests[0];
                            }
                            else {
                                return `(and ${ttests.join(" ")})`;
                            }
                        }
                    }
                    else {
                        return this.generateSubtypeTupleCheck(arg, this.typegen.typeToSMTCategory(argtype), `(bsqtuple_${SMTTypeEmitter.getTupleTypeMaxLength(argtype)}@IDX ARG)`, `(is-bsqterm@clear  (bsqtuple_${SMTTypeEmitter.getTupleTypeMaxLength(argtype)}@IDX ARG))`, argtype, oftype, gas);
                    }
                }
            }
            else {
                return this.generateSubtypeTupleCheck(arg, this.typegen.typeToSMTCategory(argtype), `(bsqtuple_${SMTTypeEmitter.getTupleTypeMaxLength(argtype)}@IDX ARG)`, `(is-bsqterm@clear  (bsqtuple_${SMTTypeEmitter.getTupleTypeMaxLength(argtype)}@IDX ARG))`, argtype, oftype, gas);
            }
        }
        else if(this.typegen.isRecordType(argtype) || this.typegen.isUEntityType(argtype)) {
            return "false"
        }
        else {
            assert(this.typegen.typeToSMTCategory(argtype) === "BTerm"); 

            const tsc = this.generateSubtypeTupleCheck(arg, "BTerm", "(select (bsqterm_tuple_entries ARG) IDX)", "(is-bsqterm@clear (select (bsqterm_tuple_entries ARG) IDX))", argtype, oftype, gas);
            return `(and (is-bsqterm_tuple ${arg}) ${tsc})`
        }
    }

    generateFastRecordTypeCheck(arg: string, argtype: MIRType, oftype: MIRRecordType, inline: boolean, gas: number): string {
        if(this.typegen.isSimpleBoolType(argtype) || this.typegen.isSimpleIntType(argtype) || this.typegen.isSimpleStringType(argtype) || this.typegen.isKeyType(argtype) || this.typegen.isTupleType(argtype)) {
            return "false";
        }
        else if (this.typegen.isRecordType(argtype)) {
            if (this.typegen.isKnownLayoutRecordType(argtype)) {
                const arecord = SMTTypeEmitter.getKnownLayoutRecordType(argtype);
                if(arecord.entries.some((entry) => oftype.entries.find((oe) => entry.name ===  oe.name) === undefined)) {
                    return "false";
                }
                else if(oftype.entries.some((entry) => !entry.isOptional && arecord.entries.find((ae) => entry.name ===  ae.name) === undefined)) {
                    return "false";
                }
                else {
                    if (inline) {
                        let ttests = arecord.entries.map((entry) => {
                            const ofentry = oftype.entries.find((oe) => oe.name === entry.name) as MIRRecordTypeEntry;
                            return this.generateTypeCheck(`(${this.typegen.generateRecordAccessor(argtype, entry.name)} ${arg})`, this.typegen.anyType, ofentry.type, false, gas)

                        });

                        if (ttests.includes("false")) {
                            return "false";
                        }
                        else {
                            ttests = ttests.filter((chk) => chk !== "true");
                            if(ttests.length === 0) {
                                return "true";
                            }
                            else if(ttests.length === 1) {
                                return ttests[0];
                            }
                            else {
                                return `(and ${ttests.join(" ")})`;
                            }
                        }
                    }
                    else {
                        return this.generateSubtypeRecordCheck(arg, this.typegen.typeToSMTCategory(argtype), `(bsqrecord_${this.typegen.generateRecordTypePropertyName(argtype)}@PNAME ARG)`, `(is-bsqterm@clear  (bsqrecord_${this.typegen.generateRecordTypePropertyName(argtype)}@PNAME ARG))`, argtype, oftype, gas);
                    }
                }
            }
            else {
                return this.generateSubtypeRecordCheck(arg, this.typegen.typeToSMTCategory(argtype), `(bsqrecord_${this.typegen.generateRecordTypePropertyName(argtype)}@PNAME ARG)`, `(is-bsqterm@clear  (bsqrecord_${this.typegen.generateRecordTypePropertyName(argtype)}@PNAME ARG))`, argtype, oftype, gas);
            }
        }
        else if(this.typegen.isUEntityType(argtype)) {
            return "false"
        }
        else {
            assert(this.typegen.typeToSMTCategory(argtype) === "BTerm"); 

            const tsc = this.generateSubtypeRecordCheck(arg, "BTerm", "(select (bsqterm_record_entries ARG) \"PNAME\")", "(is-bsqterm@clear (select (bsqterm_record_entries ARG) \"PNAME\"))", argtype, oftype, gas);
            return `(and (is-bsqterm_record ${arg}) ${tsc})`
        }
    }

    generateFastEntityTypeCheck(arg: string, argtype: MIRType, oftype: MIREntityType): string {
        if(this.typegen.isSimpleBoolType(argtype) || this.typegen.isSimpleIntType(argtype) || this.typegen.isSimpleStringType(argtype)) {
            return argtype.options[0].trkey === oftype.trkey ? "true" : "false";
        }
        else if (this.typegen.isKeyType(argtype)) {
            const ofdecl = this.typegen.assembly.entityDecls.get(oftype.ekey) as MIREntityTypeDecl;

            if(oftype.ekey === "NSCore::None") {
                return `(= ${arg} bsqkey_none)`;
            }
            else if(oftype.ekey === "NSCore::Bool") {
                return `(is-bsqkey_bool ${arg})`;
            }
            else if(oftype.ekey === "NSCore::Int") {
                return `(is-bsqkey_int ${arg})`;
            }
            else if(oftype.ekey === "NSCore::String") {
                return `(is-bsqkey_string ${arg})`;
            }
            else if(oftype.ekey.startsWith("NSCore::StringOf<")) {
                return `(and (is-bsqkey_typedstring ${arg}) (= (bsqkey_typedstring_type ${arg}) ${this.typegen.mangleStringForSMT(oftype.ekey)}))`;
            }
            else if(oftype.ekey === "NSCore::GUID") {
                return `(is-bsqkey_guid ${arg})`;
            }
            else if (ofdecl.provides.includes("NSCore::Enum")) {
                return `(and (is-bsqkey_enum ${arg}) (= (bsqkey_enum_type ${arg}) ${this.typegen.mangleStringForSMT(oftype.ekey)}))`;
            }
            else if (ofdecl.provides.includes("NSCore::IdKey")) {
                return `(and (is-bsqkey_idkey ${arg}) (= (bsqkey_idkey_type ${arg}) ${this.typegen.mangleStringForSMT(oftype.ekey)}))`;
            }
            else {
                return "false";
            }
        }
        else if(this.typegen.isTupleType(argtype) || this.typegen.isRecordType(argtype)) {
            return "false";
        }
        else if (this.typegen.isUEntityType(argtype)) {
            const ut = SMTTypeEmitter.getUEntityType(argtype);
            if(oftype.ekey === "NSCore::None") {
                return `(is-${this.typegen.generateEntityNoneConstructor(ut.ekey)} ${arg})`;
            }
            else {
                if(ut.ekey !== oftype.ekey) {
                    return "false";
                }
                else {
                    if(argtype.options.length === 1) {
                        return "true";
                    }
                    else {
                        return `(is-${this.typegen.generateEntityConstructor(ut.ekey)} ${arg})`;
                    }
                }
            }
        }
        else {
            assert(this.typegen.typeToSMTCategory(argtype) === "BTerm");

            const ofdecl = this.typegen.assembly.entityDecls.get(oftype.ekey) as MIREntityTypeDecl;

            if(oftype.ekey === "NSCore::None") {
                return `(= (bsqterm_key bsqkey_none) ${arg})`;
            }
            else if(oftype.ekey === "NSCore::Bool") {
                return `(and (is-bsqterm_key ${arg}) (is-bsqkey_bool (bsqterm_key_value ${arg})))`;
            }
            else if(oftype.ekey === "NSCore::Int") {
                return `(and (is-bsqterm_key ${arg}) (is-bsqkey_int (bsqterm_key_value ${arg})))`;
            }
            else if(oftype.ekey === "NSCore::String") {
                return `(and (is-bsqterm_key ${arg}) (is-bsqkey_string (bsqterm_key_value ${arg})))`;
            }
            else if(oftype.ekey.startsWith("NSCore::StringOf<")) {
                return `(and (is-bsqterm_key ${arg}) (is-bsqkey_typedstring (bsqterm_key_value ${arg})) (= (bsqkey_typedstring_type (bsqterm_key_value ${arg})) "${this.typegen.mangleStringForSMT(oftype.ekey)}"))`;
            }
            else if(oftype.ekey.startsWith("NSCore::POBBuffer<")) {
                return `(and (is-bsqterm_podbuffer ${arg}) (= (bsqterm_podbuffer_type ${arg}) ${this.typegen.mangleStringForSMT(oftype.ekey)}))`;
            }
            else if(oftype.ekey === "NSCore::GUID") {
                return `(and (is-bsqterm_key ${arg}) (is-bsqkey_guid (bsqterm_key_value ${arg})))`;
            }
            else if (ofdecl.provides.includes("NSCore::Enum")) {
                return `(and (is-bsqterm_key ${arg}) (is-bsqkey_enum (bsqterm_key_value ${arg})) (= (bsqkey_enum_type (bsqterm_key_value ${arg})) "${this.typegen.mangleStringForSMT(oftype.ekey)}"))`;
            }
            else if (ofdecl.provides.includes("NSCore::IdKey")) {
                return `(and (is-bsqterm_key ${arg}) (is-bsqkey_idkey (bsqterm_key_value ${arg})) (= (bsqkey_idkey_type (bsqterm_key_value ${arg})) "${this.typegen.mangleStringForSMT(oftype.ekey)}"))`;
            }
            else if(oftype.ekey === "NSCore::Regex") {
                return `(is-bsqterm_regex ${arg})`;
            }
            else {
                if (oftype.ekey.startsWith("NSCore::List<")) {
                    return `(and (is-bsqterm_list ${arg}) (= (bsqterm_list_type ${arg}) "${oftype.ekey}"))`;
                }
                else if (oftype.ekey.startsWith("NSCore::Set<") || oftype.ekey.startsWith("NSCore::Map<")) {
                    return `(and (is-bsqterm_kvcontainer ${arg}) (= (bsqterm_kvcontainer_type ${arg}) "${oftype.ekey}"))`;
                }
                else {
                    return `(and (is-bsqterm_object ${arg}) (= (bsqterm_object_type ${arg}) "${oftype.ekey}"))`;
                }
            }
        }
    }

    generateFastConceptTypeCheck(arg: string, argtype: MIRType, oftype: MIRConceptType): string {
        const cpttype = this.typegen.getMIRType(oftype.trkey);

        if(oftype.trkey === "NSCore::Any") {
            return "true";
        }

        if(oftype.trkey === "NSCore::Some") {
            if (!this.typegen.assembly.subtypeOf(this.typegen.noneType, argtype)) {
                return "true";
            }
            else if (this.typegen.isKeyType(argtype)) {
                return `(not (= ${arg} bsqkey_none))`;
            }
            else if (this.typegen.isUEntityType(argtype)) {
                return `(is-${this.typegen.generateEntityConstructor(SMTTypeEmitter.getUEntityType(argtype).ekey)} ${arg})`;
            }
            else {
                return `(not (= (bsqterm_key bsqkey_none) ${arg}))`;
            }
        }

        if(this.typegen.isSimpleBoolType(argtype)) {
            return this.typegen.assembly.subtypeOf(this.typegen.boolType, cpttype) ? "true" : "false";
        }
        else if(this.typegen.isSimpleIntType(argtype)) {
            return this.typegen.assembly.subtypeOf(this.typegen.intType, cpttype) ? "true" : "false";
        }
        else if(this.typegen.isSimpleStringType(argtype)) {
            return this.typegen.assembly.subtypeOf(this.typegen.stringType, cpttype) ? "true" : "false";
        }
        else if(this.typegen.isKeyType(argtype)) {
            if(oftype.trkey === "NSCore::KeyType") {
                return "true";
            }
            
            let checks: string[] = [];

            if (this.typegen.assembly.subtypeOf(this.typegen.noneType, cpttype)) {
                if (this.typegen.assembly.subtypeOf(this.typegen.noneType, argtype)) {
                    checks.push(`(= bsqkey_none ${arg})`);
                }
            }

            if(this.typegen.assembly.subtypeOf(this.typegen.boolType, cpttype)) {
                if (this.typegen.assembly.subtypeOf(this.typegen.boolType, argtype)) {
                    checks.push(`(is-bsqkey_bool ${arg})`);
                }
            }

            if(this.typegen.assembly.subtypeOf(this.typegen.intType, cpttype)) {
                if (this.typegen.assembly.subtypeOf(this.typegen.intType, argtype)) {
                    checks.push(`(is-bsqkey_int ${arg})`);
                }
            }

            if (this.typegen.assembly.subtypeOf(this.typegen.stringType, cpttype)) {
                if (this.typegen.assembly.subtypeOf(this.typegen.stringType, argtype)) {
                    checks.push(`(is-bsqkey_string ${arg})`);
                }
            }

            if (this.typegen.maybeOfType_StringOf(cpttype)) {
                if (this.typegen.maybeOfType_StringOf(argtype)) {
                    const taccess = `(bsqkey_typedstring_type ${arg})`;
                    checks.push(`(and (is-bsqkey_typedstring ${arg}) ${this.typegen.generateCheckSubtype(taccess, oftype)})`);
                }
            }

            if (this.typegen.assembly.subtypeOf(this.typegen.getMIRType("NSCore::GUID"), cpttype)) {
                if (this.typegen.assembly.subtypeOf(this.typegen.getMIRType("NSCore::GUID"), argtype)) {
                    checks.push(`(is-bsqkey_guid ${arg})`);
                }
            }

            if (this.typegen.maybeOfType_Enum(cpttype)) {
                if (this.typegen.maybeOfType_Enum(argtype)) {
                    const taccess = `(bsqkey_enum_type ${arg})`;
                    checks.push(`(and (is-bsqkey_enum ${arg}) ${this.typegen.generateCheckSubtype(taccess, oftype)})`);
                }
            }

            if (this.typegen.maybeOfType_IdKey(cpttype)) {
                if (this.typegen.maybeOfType_IdKey(argtype)) {
                    const taccess = `(bsqkey_idkey_type ${arg})`;
                    checks.push(`(and (is-bsqkey_idkey ${arg}) ${this.typegen.generateCheckSubtype(taccess, oftype)})`);
                }
            }

            
            if (checks.length === 0) {
                return "false";
            }
            else if (checks.length === 1) {
                return checks[0];
            }
            else {
                return `(or ${checks.join(" ")})`;
            }
        }
        else if(this.typegen.isTupleType(argtype)) {
            return this.typegen.assembly.subtypeOf(this.typegen.getMIRType("NSCore::Tuple"), cpttype) ? "true" : "false";
        }
        else if(this.typegen.isRecordType(argtype)) {
            return this.typegen.assembly.subtypeOf(this.typegen.getMIRType("NSCore::Record"), cpttype) ? "true" : "false";
        }
        else if (this.typegen.isUEntityType(argtype)) {
            const etype = this.typegen.getMIRType(SMTTypeEmitter.getUEntityType(argtype).trkey);
            if (this.typegen.assembly.subtypeOf(this.typegen.noneType, cpttype) && this.typegen.assembly.subtypeOf(etype, cpttype)) {
                return "true";
            }
            else if(!this.typegen.assembly.subtypeOf(this.typegen.noneType, cpttype) && this.typegen.assembly.subtypeOf(etype, cpttype)) {
                if(this.typegen.assembly.subtypeOf(this.typegen.noneType, argtype)) {
                    return `(is-${this.typegen.generateEntityConstructor(etype.trkey)} ${arg})`;
                }
                else {
                    return "true";
                }
            }
            else if (this.typegen.assembly.subtypeOf(this.typegen.noneType, cpttype) && !this.typegen.assembly.subtypeOf(etype, cpttype)) {
                return `(is-${this.typegen.generateEntityConstructor(etype.trkey)} ${arg})`;
            }
            else {
                return "false";
            }
        }
        else {
            let checks: string[] = [];

            if (this.typegen.assembly.subtypeOf(this.typegen.noneType, cpttype)) {
                if (this.typegen.assembly.subtypeOf(this.typegen.noneType, argtype)) {
                    checks.push(`(= (bsqterm_key bsqkey_none) ${arg})`);
                }
            }

            if(this.typegen.assembly.subtypeOf(this.typegen.boolType, cpttype)) {
                if (this.typegen.assembly.subtypeOf(this.typegen.boolType, argtype)) {
                    checks.push(`(and (is-bsqterm_key ${arg}) (is-bsqkey_bool (bsqterm_key_value ${arg})))`);
                }
            }

            if(this.typegen.assembly.subtypeOf(this.typegen.intType, cpttype)) {
                if (this.typegen.assembly.subtypeOf(this.typegen.intType, argtype)) {
                    checks.push(`(and (is-bsqterm_key ${arg}) (is-bsqkey_int (bsqterm_key_value ${arg})))`);
                }
            }

            if (this.typegen.assembly.subtypeOf(this.typegen.stringType, cpttype)) {
                if (this.typegen.assembly.subtypeOf(this.typegen.stringType, argtype)) {
                    checks.push(`(and (is-bsqterm_key ${arg}) (is-bsqkey_string (bsqterm_key_value ${arg})))`);
                }
            }

            if (this.typegen.maybeOfType_StringOf(cpttype)) {
                if (this.typegen.maybeOfType_StringOf(argtype)) {
                    const taccess = `(bsqkey_typedstring_type (bsqterm_key_value ${arg}))`;
                    checks.push(`(and (is-bsqterm_key ${arg}) (is-bsqkey_typedstring (bsqterm_key_value ${arg})) ${this.typegen.generateCheckSubtype(taccess, oftype)})`);
                }
            }

            if (this.typegen.maybeOfType_PODBuffer(cpttype)) {
                if (this.typegen.maybeOfType_PODBuffer(argtype)) {
                    const taccess = `(bsqkey_podbuffer_type (bsqterm_key_value ${arg}))`;
                    checks.push(`(and (is-bsqterm_key ${arg}) (is-bsqkey_podbuffer (bsqterm_key_value ${arg})) ${this.typegen.generateCheckSubtype(taccess, oftype)})`);
                }
            }

            if (this.typegen.assembly.subtypeOf(this.typegen.getMIRType("NSCore::GUID"), cpttype)) {
                if (this.typegen.assembly.subtypeOf(this.typegen.getMIRType("NSCore::GUID"), argtype)) {
                    checks.push(`(and (is-bsqterm_key ${arg}) (is-bsqkey_guid (bsqterm_key_value ${arg})))`);
                }
            }

            if (this.typegen.maybeOfType_Enum(cpttype)) {
                if (this.typegen.maybeOfType_Enum(argtype)) {
                    const taccess = `(bsqkey_enum_type (bsqterm_key_value ${arg}))`;
                    checks.push(`(and (is-bsqterm_key ${arg}) (is-bsqkey_enum (bsqterm_key_value ${arg})) ${this.typegen.generateCheckSubtype(taccess, oftype)})`);
                }
            }

            if (this.typegen.maybeOfType_IdKey(cpttype)) {
                if (this.typegen.maybeOfType_IdKey(argtype)) {
                    const taccess = `(bsqkey_idkey_type (bsqterm_key_value ${arg}))`;
                    checks.push(`(and (is-bsqterm_key ${arg}) (is-bsqkey_idkey (bsqterm_key_value ${arg})) ${this.typegen.generateCheckSubtype(taccess, oftype)})`);
                }
            }

            if (this.typegen.assembly.subtypeOf(this.typegen.getMIRType("NSCore::Tuple"), cpttype)) {
                if (argtype.options.some((topt) => topt instanceof MIRTupleType)) {
                    checks.push(`(is-bsqterm_tuple ${arg})`);
                }
            }

            if (this.typegen.assembly.subtypeOf(this.typegen.getMIRType("NSCore::Record"), cpttype)) {
                if (argtype.options.some((topt) => topt instanceof MIRTupleType)) {
                    checks.push(`(is-bsqterm_record ${arg})`);
                }
            }

            if (this.typegen.maybeOfType_Object(cpttype)) {
                if (this.typegen.maybeOfType_Object(argtype)) {
                    const taccess = `(bsqterm_object_type ${arg})`;
                    checks.push(`(and (is-bsqterm_object ${arg}) ${this.typegen.generateCheckSubtype(taccess, oftype)})`);
                }
            }

            if (this.typegen.maybeOfType_List(cpttype)) {
                if (this.typegen.maybeOfType_List(argtype)) {
                    const taccess = `(bsqterm_list_type ${arg})`;
                    checks.push(`(and (is-bsqterm_list ${arg}) ${this.typegen.generateCheckSubtype(taccess, oftype)})`);
                }
            }

            if (this.typegen.maybeOfType_Set(cpttype)) {
                if (this.typegen.maybeOfType_Set(argtype)) {
                    const taccess = `(bsqterm_kvcontainer_type ${arg})`;
                    checks.push(`(and (is-bsqterm_kvcontainer ${arg}) ${this.typegen.generateCheckSubtype(taccess, oftype)})`);
                }
            }

            if (this.typegen.maybeOfType_Map(cpttype)) {
                if (this.typegen.maybeOfType_Map(argtype)) {
                    const taccess = `(bsqterm_kvcontainer_type ${arg})`;
                    checks.push(`(and (is-bsqterm_kvcontainer ${arg}) ${this.typegen.generateCheckSubtype(taccess, oftype)})`);
                }
            }

            if (checks.length === 0) {
                return "false";
            }
            else if (checks.length === 1) {
                return checks[0];
            }
            else {
                return `(or ${checks.join(" ")})`;
            }
        }
    }

    generateTypeCheck(arg: string, argtype: MIRType, oftype: MIRType, inline: boolean, gas: number): string {
        if(this.typegen.assembly.subtypeOf(argtype, oftype)) {
            return "true";
        }

        const tests = oftype.options.map((topt) => {
            const mtype = this.typegen.getMIRType(topt.trkey);
            assert(mtype !== undefined, "We should generate all the component types by default??");

            if(topt instanceof MIREntityType) {
                return this.generateFastEntityTypeCheck(arg, argtype, topt);
            }
            else if (topt instanceof MIRConceptType) {
                return this.generateFastConceptTypeCheck(arg, argtype, topt);
            }
            else if (topt instanceof MIRTupleType) {
                return this.generateFastTupleTypeCheck(arg, argtype, topt, inline, gas);
            }
            else {
                assert(topt instanceof MIRRecordType);

                return this.generateFastRecordTypeCheck(arg, argtype, topt as MIRRecordType, inline, gas);
            }
        })
        .filter((test) => test !== "false");

        if(tests.length === 0) {
            return "false";
        }
        else if(tests.includes("true")) {
            return "true";
        }
        else if(tests.length === 1) {
            return tests[0];
        }
        else {
            return `(or ${tests.join(" ")})`
        }
    }

    generateStmt(op: MIROp, fromblck: string, gas: number | undefined): SMTExp | undefined {
        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const lcv = op as MIRLoadConst;
                return new SMTLet(this.varToSMTName(lcv.trgt), this.generateConstantExp(lcv.src, this.getArgType(lcv.trgt)));
            }
            case MIROpTag.MIRLoadConstTypedString:  {
                return this.generateLoadConstTypedString(op as MIRLoadConstTypedString);
            }
            case MIROpTag.MIRAccessConstantValue: {
                const acv = (op as MIRAccessConstantValue);
                return this.generateAccessConstantValue(acv);
            }
            case MIROpTag.MIRLoadFieldDefaultValue: {
                const ldv = (op as MIRLoadFieldDefaultValue);
                return this.generateLoadFieldDefaultValue(ldv);
            }
            case MIROpTag.MIRAccessArgVariable: {
                const lav = op as MIRAccessArgVariable;
                return new SMTLet(this.varToSMTName(lav.trgt), this.argToSMT(lav.name, this.getArgType(lav.trgt)));
            }
            case MIROpTag.MIRAccessLocalVariable: {
                const llv = op as MIRAccessLocalVariable;
                return new SMTLet(this.varToSMTName(llv.trgt), this.argToSMT(llv.name, this.getArgType(llv.trgt)));
            }
            case MIROpTag.MIRConstructorPrimary: {
                const cp = op as MIRConstructorPrimary;
                return this.generateMIRConstructorPrimary(cp);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
                const cpce = op as MIRConstructorPrimaryCollectionEmpty;
                return this.generateMIRConstructorPrimaryCollectionEmpty(cpce);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                const cpcs = op as MIRConstructorPrimaryCollectionSingletons;
                return this.generateMIRConstructorPrimaryCollectionSingletons(cpcs);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionCopies: {
                return NOT_IMPLEMENTED<SMTExp>("MIRConstructorPrimaryCollectionCopies");
            }
            case MIROpTag.MIRConstructorPrimaryCollectionMixed: {
                return NOT_IMPLEMENTED<SMTExp>("MIRConstructorPrimaryCollectionMixed");
            }
            case MIROpTag.MIRConstructorTuple: {
                const tc = op as MIRConstructorTuple;
                return this.generateMIRConstructorTuple(tc);
            }
            case MIROpTag.MIRConstructorRecord: {
                const tr = op as MIRConstructorRecord;
                return this.generateMIRConstructorRecord(tr);
            }
            case MIROpTag.MIRConstructorEphemeralValueList: {
                const te = op as MIRConstructorEphemeralValueList;
                return this.generateMIRConstructorEphemeralValueList(te);
            }
            case MIROpTag.MIRAccessFromIndex: {
                const ai = op as MIRAccessFromIndex;
                return new SMTLet(this.varToSMTName(ai.trgt), this.generateMIRAccessFromIndexExpression(ai.arg, ai.idx, this.typegen.getMIRType(ai.resultAccessType)));
            }
            case MIROpTag.MIRProjectFromIndecies: {
                const pi = op as MIRProjectFromIndecies;
                return this.generateMIRProjectFromIndecies(pi, this.typegen.getMIRType(pi.resultProjectType));
            }
            case MIROpTag.MIRAccessFromProperty: {
                const ap = op as MIRAccessFromProperty;
                return new SMTLet(this.varToSMTName(ap.trgt), this.generateMIRAccessFromPropertyExpression(ap.arg, ap.property, this.typegen.getMIRType(ap.resultAccessType)));
            }
            case MIROpTag.MIRProjectFromProperties: {
                const pp = op as MIRProjectFromProperties;
                return this.generateMIRProjectFromProperties(pp, this.typegen.getMIRType(pp.resultProjectType));
            }
            case MIROpTag.MIRAccessFromField: {
                const af = op as MIRAccessFromField;
                return this.generateMIRAccessFromField(af, this.typegen.getMIRType(af.resultAccessType));
            }
            case MIROpTag.MIRProjectFromFields: {
                const pf = op as MIRProjectFromFields;
                return this.generateMIRProjectFromFields(pf);
            }
            case MIROpTag.MIRProjectFromTypeTuple: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromTypeTuple");
            }
            case MIROpTag.MIRProjectFromTypeRecord: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromTypeRecord");
            }
            case MIROpTag.MIRProjectFromTypeNominal: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromTypeConcept");
            }
            case MIROpTag.MIRModifyWithIndecies: {
                const mi = op as MIRModifyWithIndecies;
                return this.generateMIRModifyWithIndecies(mi, this.typegen.getMIRType(mi.resultTupleType));
            }
            case MIROpTag.MIRModifyWithProperties: {
                const mp = op as MIRModifyWithProperties;
                return this.generateMIRModifyWithProperties(mp, this.typegen.getMIRType(mp.resultRecordType));
            }
            case MIROpTag.MIRModifyWithFields: {
                const mf = op as MIRModifyWithFields;
                return this.generateMIRModifyWithFields(mf);
            }
            case MIROpTag.MIRStructuredExtendTuple: {
                const si = op as MIRStructuredExtendTuple;
                return this.generateMIRStructuredExtendTuple(si, this.typegen.getMIRType(si.resultTupleType));
            }
            case MIROpTag.MIRStructuredExtendRecord: {
                const sp = op as MIRStructuredExtendRecord;
                return this.generateMIRStructuredExtendRecord(sp, this.typegen.getMIRType(sp.resultRecordType));
            }
            case MIROpTag.MIRStructuredExtendObject: {
                const so = op as MIRStructuredExtendObject;
                return this.generateMIRStructuredExtendObject(op);
            }
            case MIROpTag.MIRInvokeFixedFunction: {
                const invk = op as MIRInvokeFixedFunction;
                return this.generateMIRInvokeFixedFunction(invk, gas);
            }
            case MIROpTag.MIRInvokeVirtualTarget: {
                return NOT_IMPLEMENTED<SMTExp>("MIRInvokeVirtualTarget");
            }
            case MIROpTag.MIRPrefixOp: {
                const pfx = op as MIRPrefixOp;
                if (pfx.op === "!") {
                    const tval = this.generateTruthyConvert(pfx.arg);
                    return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`(not ${tval.emit()})`));
                }
                else {
                    if (pfx.op === "-") {
                        if (pfx.arg instanceof MIRConstantInt) {
                            return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`-${(pfx.arg as MIRConstantInt).value}`));
                        }
                        else {
                            return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`(* -1 ${this.argToSMT(pfx.arg, this.typegen.intType).emit()})`));
                        }
                    }
                    else {
                        return new SMTLet(this.varToSMTName(pfx.trgt), this.argToSMT(pfx.arg, this.typegen.intType));
                    }
                }
            }
            case MIROpTag.MIRBinOp: {
                const bop = op as MIRBinOp;

                if (bop.op === "*") {
                    if(bop.rhs instanceof MIRConstantInt || bop.lhs instanceof MIRConstantInt) {
                        return new SMTLet(this.varToSMTName(bop.trgt), new SMTValue(`(* ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                    }
                    else {
                        return new SMTLet(this.varToSMTName(bop.trgt), new SMTValue(`(mult_op ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                    }
                }
                else if (bop.op === "/") {
                    if (bop.rhs instanceof MIRConstantInt || bop.lhs instanceof MIRConstantInt) {
                        const divres = new SMTLet(this.varToSMTName(bop.trgt), new SMTValue(`(/ ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                        return new SMTCond(new SMTValue(`(= ${this.argToSMT(bop.rhs, this.typegen.intType).emit()} 0)`), this.generateErrorCreate(op.sinfo, this.typegen.typeToSMTCategory(this.currentRType)), divres);
                    }
                    else {
                        const divres = new SMTLet(this.varToSMTName(bop.trgt), new SMTValue(`(div_op ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                        return new SMTCond(new SMTValue(`(= ${this.argToSMT(bop.rhs, this.typegen.intType).emit()} 0)`), this.generateErrorCreate(op.sinfo, this.typegen.typeToSMTCategory(this.currentRType)), divres);
                    }
                }
                else if (bop.op === "%") {
                    const modres = new SMTLet(this.varToSMTName(bop.trgt), new SMTValue(`(mod_op ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                    return new SMTCond(new SMTValue(`(= ${this.argToSMT(bop.rhs, this.typegen.intType).emit()} 0)`), this.generateErrorCreate(op.sinfo, this.typegen.typeToSMTCategory(this.currentRType)), modres);
                }
                else {
                    return new SMTLet(this.varToSMTName(bop.trgt), new SMTValue(`(${bop.op} ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                }
            }
            case MIROpTag.MIRGetKey: {
                return NOT_IMPLEMENTED<SMTExp>("MIRGetKey");
            }
            case MIROpTag.MIRBinEq: {
                const beq = op as MIRBinEq;

                const lhvtypeinfer = this.typegen.getMIRType(beq.lhsInferType);
                const rhvtypeinfer = this.typegen.getMIRType(beq.rhsInferType);
                return new SMTLet(this.varToSMTName(beq.trgt), new SMTValue(this.generateEquals(beq.op, lhvtypeinfer, beq.lhs, rhvtypeinfer, beq.rhs)));
            }
            case MIROpTag.MIRBinCmp: {
                const bcmp = op as MIRBinCmp;

                const lhvtypeinfer = this.typegen.getMIRType(bcmp.lhsInferType);
                const rhvtypeinfer = this.typegen.getMIRType(bcmp.rhsInferType);
                return new SMTLet(this.varToSMTName(bcmp.trgt), new SMTValue(this.generateCompare(bcmp.op, lhvtypeinfer, bcmp.lhs, rhvtypeinfer, bcmp.rhs)));
            }
            case MIROpTag.MIRIsTypeOfNone: {
                const ton = op as MIRIsTypeOfNone;
                return new SMTLet(this.varToSMTName(ton.trgt), this.generateNoneCheck(ton.arg));
            }
            case MIROpTag.MIRIsTypeOfSome: {
                const tos = op as MIRIsTypeOfSome;
                return new SMTLet(this.varToSMTName(tos.trgt), new SMTValue(`(not ${this.generateNoneCheck(tos.arg).emit()})`));
           }
            case MIROpTag.MIRIsTypeOf: {
                const top = op as MIRIsTypeOf;
                const oftype = this.typegen.getMIRType(top.oftype);
                const argtype = this.getArgType(top.arg);

                return new SMTLet(this.varToSMTName(top.trgt), new SMTValue(this.generateTypeCheck(this.argToSMT(top.arg, argtype).emit(), argtype, oftype, true, this.typecheckgas)));
            }
            case MIROpTag.MIRRegAssign: {
                const regop = op as MIRRegAssign;
                return new SMTLet(this.varToSMTName(regop.trgt), this.argToSMT(regop.src, this.getArgType(regop.trgt)));
            }
            case MIROpTag.MIRTruthyConvert: {
                const tcop = op as MIRTruthyConvert;
                return new SMTLet(this.varToSMTName(tcop.trgt), this.generateTruthyConvert(tcop.src));
            }
            case MIROpTag.MIRLogicStore: {
                const llop = op as MIRLogicStore;
                return new SMTLet(this.varToSMTName(llop.trgt), new SMTValue(`(${llop.op === "&" ? "and" : "or"} ${this.argToSMT(llop.lhs, this.typegen.boolType).emit()} ${this.argToSMT(llop.rhs, this.typegen.boolType).emit()})`));
            }
            case MIROpTag.MIRVarStore: {
                const vsop = op as MIRVarStore;
                return new SMTLet(this.varToSMTName(vsop.name), this.argToSMT(vsop.src, this.getArgType(vsop.name)));
            }
            case MIROpTag.MIRReturnAssign: {
                const raop = op as MIRReturnAssign;
                return new SMTLet(this.varToSMTName(raop.name), this.argToSMT(raop.src, this.getArgType(raop.name)));
            }
            case MIROpTag.MIRAbort: {
                const aop = (op as MIRAbort);
                return this.generateErrorCreate(aop.sinfo, this.typegen.typeToSMTCategory(this.currentRType));
            }
            case MIROpTag.MIRDebug: {
                return undefined;
            }
            case MIROpTag.MIRJump: {
                return undefined;
            }
            case MIROpTag.MIRJumpCond: {
                const cjop = op as MIRJumpCond;
                const smttest = this.generateTruthyConvert(cjop.arg);
                return new SMTCond(smttest, SMTFreeVar.generate("#true_trgt#"), SMTFreeVar.generate("#false_trgt#"));
            }
            case MIROpTag.MIRJumpNone: {
                const njop = op as MIRJumpNone;
                return new SMTCond(this.generateNoneCheck(njop.arg), SMTFreeVar.generate("#true_trgt#"), SMTFreeVar.generate("#false_trgt#"));
            }
            case MIROpTag.MIRPhi: {
                const pop = op as MIRPhi;
                const uvar = pop.src.get(fromblck) as MIRRegisterArgument;

                return new SMTLet(this.varToSMTName(pop.trgt), this.argToSMT(uvar, this.getArgType(pop.trgt)));
            }
            case MIROpTag.MIRVarLifetimeStart:
            case MIROpTag.MIRVarLifetimeEnd: {
                return undefined;
            }
            default: {
                return NOT_IMPLEMENTED<SMTExp>(`Missing case ${op.tag}`);
            }
        }
    }

    generateBlockExps(block: MIRBasicBlock, fromblock: string, blocks: Map<string, MIRBasicBlock>, gas: number | undefined): SMTExp {
        const exps: SMTExp[] = [];
        for (let i = 0; i < block.ops.length; ++i) {
            const exp = this.generateStmt(block.ops[i], fromblock, gas);
            if (exp !== undefined) {
                exps.push(exp);
            }
        }

        if (block.label === "exit") {
            const resulttype = this.typegen.typeToSMTCategory(this.currentRType);
            let rexp = new SMTValue(`(result_success@${resulttype} _return_)`) as SMTExp;
            for (let i = exps.length - 1; i >= 0; --i) {
                rexp = exps[i].bind(rexp, "#body#");
            }

            return rexp;
        }
        else {
            const jop = block.ops[block.ops.length - 1];
            if (jop.tag === MIROpTag.MIRJump) {
                let rexp = this.generateBlockExps(blocks.get((jop as MIRJump).trgtblock) as MIRBasicBlock, block.label, blocks, gas);
                for (let i = exps.length - 1; i >= 0; --i) {
                    rexp = exps[i].bind(rexp, "#body#");
                }

                return rexp;
            }
            else {
                assert(jop.tag === MIROpTag.MIRJumpCond || jop.tag === MIROpTag.MIRJumpNone);

                let tblock = ((jop.tag === MIROpTag.MIRJumpCond) ? blocks.get((jop as MIRJumpCond).trueblock) : blocks.get((jop as MIRJumpNone).noneblock)) as MIRBasicBlock;
                let texp = this.generateBlockExps(tblock, block.label, blocks, gas);

                let fblock = ((jop.tag === MIROpTag.MIRJumpCond) ? blocks.get((jop as MIRJumpCond).falseblock) : blocks.get((jop as MIRJumpNone).someblock)) as MIRBasicBlock;
                let fexp = this.generateBlockExps(fblock, block.label, blocks, gas);

                let rexp = exps[exps.length - 1].bind(texp, "#true_trgt#").bind(fexp, "#false_trgt#");
                for (let i = exps.length - 2; i >= 0; --i) {
                    rexp = exps[i].bind(rexp, "#body#");
                }

                return rexp;
            }
        }
    }

    generateSMTInvoke(idecl: MIRInvokeDecl, cscc: Set<string>, gas: number | undefined, gasdown: number | undefined): string {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.getMIRType(idecl.resultType);
        this.currentSCC = cscc;

        let argvars = new Map<string, MIRType>();
        idecl.params.forEach((arg) => argvars.set(arg.name, this.assembly.typeMap.get(arg.type) as MIRType));

        const args = idecl.params.map((arg) => `(${this.varNameToSMTName(arg.name)} ${this.typegen.typeToSMTCategory(this.typegen.getMIRType(arg.type))})`);
        const restype = this.typegen.typeToSMTCategory(this.typegen.getMIRType(idecl.resultType));
        const decl = `(define-fun ${this.invokenameToSMT(idecl.key)}${gas !== undefined ? `@gas${gas}` : ""} (${args.join(" ")}) Result@${restype}`;

        if (idecl instanceof MIRInvokeBodyDecl) {
            this.vtypes = new Map<string, MIRType>();
            (idecl.body.vtypes as Map<string, string>).forEach((tkey, name) => {
                this.vtypes.set(name, this.typegen.getMIRType(tkey));
            });

            const blocks = (idecl as MIRInvokeBodyDecl).body.body;
            const body = this.generateBlockExps(blocks.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocks, gasdown);

            if (idecl.preconditions.length === 0 && idecl.postconditions.length === 0) {
                return `${decl} \n${body.emit("  ")})`;
            }
            else {
                let cbody = body;

                if (idecl.postconditions.length !== 0) {
                    //
                    //TODO -- ref parms don't get expanded correctly here -- need to coordinate with def and call here
                    //
                    const tbody = this.generateTempName();
                    const postinvoke = this.invokenameToSMT(MIRKeyGenerator.generateBodyKey("post", idecl.key));
                    const callpost = new SMTValue(`(${postinvoke} ${idecl.params.map((arg) => this.varNameToSMTName(arg.name)).join(" ")} (result_success_value@${restype} ${tbody}))`);
                    cbody = new SMTLet(tbody, new SMTValue(cbody.emit("  ")), new SMTCond(callpost, new SMTValue(tbody), this.generateErrorCreate(idecl.sourceLocation, restype)));
                }

                if (idecl.preconditions.length !== 0) {
                    const preinvoke = this.invokenameToSMT(MIRKeyGenerator.generateBodyKey("pre", idecl.key));
                    const callpre = new SMTValue(idecl.params.length !== 0 ? `(${preinvoke} ${idecl.params.map((arg) => this.varNameToSMTName(arg.name)).join(" ")})` : preinvoke);
                    cbody = new SMTCond(callpre, cbody, this.generateErrorCreate(idecl.sourceLocation, restype));
                }

                return `${decl} \n${cbody.emit("  ")})`;
            }
        }
        else {
            assert(idecl instanceof MIRInvokePrimitiveDecl);

            const params = idecl.params.map((arg) => this.varNameToSMTName(arg.name));
            return `${decl} \n  ${this.generateBuiltinBody(idecl as MIRInvokePrimitiveDecl, params).emit("  ")}\n)`;
        }
    }

    generateSMTPre(prekey: MIRBodyKey, idecl: MIRInvokeDecl): string {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.boolType;

        const args = idecl.params.map((arg) => `(${this.varNameToSMTName(arg.name)} ${this.typegen.typeToSMTCategory(this.typegen.getMIRType(arg.type))})`);
        const decl = `(define-fun ${this.invokenameToSMT(prekey)} (${args.join(" ")}) Bool`;

        const decls = idecl.preconditions.map((pc, i) => {
            this.vtypes = new Map<string, MIRType>();
            (pc[0].vtypes as Map<string, string>).forEach((tkey, name) => {
                this.vtypes.set(name, this.typegen.getMIRType(tkey));
            });

            const blocksi = pc[0].body;
            const bodyi = this.generateBlockExps(blocksi.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocksi, undefined);
            const decli = `(define-fun ${this.invokenameToSMT(prekey)}$${i} (${args.join(" ")}) Result@Bool \n${bodyi.emit("  ")})`;
            const calli = (`(${this.invokenameToSMT(prekey)}$${i} ${idecl.params.map((p) => this.varNameToSMTName(p.name)).join(" ")})`);

            return [decli, calli];
        });

        const declsand = decls.map((cc) => {
            const tv = `@tmpvarda@${this.tmpvarctr++}`;
            return new SMTLet(tv, new SMTValue(cc[1]), new SMTValue(`(and (is-result_success@Bool ${tv}) (result_success_value@Bool ${tv}))`)).emit();
        });

        const rbody = declsand.length === 1 ? declsand[0] : `(and ${declsand.join(" ")})`;
        return `${decls.map((cc) => cc[0]).join("\n")}\n\n${decl}\n${rbody}\n)\n`;
    }

    generateSMTPost(postkey: MIRBodyKey, idecl: MIRInvokeDecl): string {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.boolType;
        const restype = this.typegen.getMIRType(idecl.resultType);

        const args = idecl.params.map((arg) => `(${this.varNameToSMTName(arg.name)} ${this.typegen.typeToSMTCategory(this.typegen.getMIRType(arg.type))})`);
        args.push(`(__result__ ${this.typegen.typeToSMTCategory(restype)})`);
        const decl = `(define-fun ${this.invokenameToSMT(postkey)} (${args.join(" ")}) Bool`;

        const decls = idecl.postconditions.map((pc, i) => {
            this.vtypes = new Map<string, MIRType>();
            (pc.vtypes as Map<string, string>).forEach((tkey, name) => {
                this.vtypes.set(name, this.typegen.getMIRType(tkey));
            });

            const blocksi = pc.body;
            const bodyi = this.generateBlockExps(blocksi.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocksi, undefined);
            const decli = `(define-fun ${this.invokenameToSMT(postkey)}$${i} (${args.join(" ")}) Result@Bool \n${bodyi.emit("  ")})`;
            const calli = (`(${this.invokenameToSMT(postkey)}$${i} ${[idecl.params.map((p) => this.varNameToSMTName(p.name)), "__result__"].join(" ")})`);

            return [decli, calli];
        });

        const declsand = decls.map((cc) => {
            const tv = `@tmpvarda@${this.tmpvarctr++}`;
            return new SMTLet(tv, new SMTValue(cc[1]), new SMTValue(`(and (is-result_success@Bool ${tv}) (result_success_value@Bool ${tv}))`)).emit();
        });

        const rbody = declsand.length === 1 ? declsand[0] : `(and ${declsand.join(" ")})`;
        return `${decls.map((cc) => cc[0]).join("\n")}\n\n${decl}\n${rbody})\n`;
    }

    generateSMTInv(invkey: MIRBodyKey, idecl: MIREntityTypeDecl): string {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.boolType;

        const args = `(${this.varNameToSMTName("this")} ${this.typegen.typeToSMTCategory(this.typegen.getMIRType(idecl.tkey))})`;
        const decl = `(define-fun ${this.invokenameToSMT(invkey)} (${args}) Bool`;

        const decls = idecl.invariants.map((pc, i) => {
            this.vtypes = new Map<string, MIRType>();
            (pc.vtypes as Map<string, string>).forEach((tkey, name) => {
                this.vtypes.set(name, this.typegen.getMIRType(tkey));
            });

            const blocksi = pc.body;
            const bodyi = this.generateBlockExps(blocksi.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocksi, undefined);
            const decli = `(define-fun ${this.invokenameToSMT(invkey)}$${i} (${args}) Result@Bool \n${bodyi.emit("  ")})`;
            const calli = (`(${this.invokenameToSMT(invkey)}$${i} ${this.varNameToSMTName("this")})`);

            return [decli, calli];
        });

        const declsand = decls.map((cc) => {
            const tv = `@tmpvarda@${this.tmpvarctr++}`;
            return new SMTLet(tv, new SMTValue(cc[1]), new SMTValue(`(and (is-result_success@Bool ${tv}) (result_success_value@Bool ${tv}))`)).emit();
        });

        const rbody = declsand.length === 1 ? declsand[0] : `(and ${declsand.join(" ")})`;
        return `${decls.map((cc) => cc[0]).join("\n")}\n\n${decl}\n${rbody})\n`;
    }

    generateSMTConst(constkey: MIRBodyKey, cdecl: MIRConstantDecl): string | undefined {
        this.currentFile = cdecl.srcFile;
        this.currentRType = this.typegen.getMIRType(cdecl.declaredType);

        if (SMTBodyEmitter.expBodyTrivialCheck(cdecl.value as MIRBody)) {
            return undefined;
        }

        this.vtypes = new Map<string, MIRType>();
        (cdecl.value.vtypes as Map<string, string>).forEach((tkey, name) => {
            this.vtypes.set(name, this.typegen.getMIRType(tkey));
        });

        const restype = this.typegen.typeToSMTCategory(this.typegen.getMIRType(cdecl.declaredType));
        const decl = `(define-fun ${this.invokenameToSMT(constkey)} () Result@${restype}`;
        const blocks = cdecl.value.body;
        const body = this.generateBlockExps(blocks.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocks, undefined);
        return `${decl} \n${body.emit("  ")})`;
    }

    generateSMTFDefault(fdkey: MIRBodyKey, fdecl: MIRFieldDecl): string | undefined {
        this.currentFile = fdecl.srcFile;
        this.currentRType = this.typegen.getMIRType(fdecl.declaredType);

        if (SMTBodyEmitter.expBodyTrivialCheck(fdecl.value as MIRBody)) {
            return undefined;
        }

        this.vtypes = new Map<string, MIRType>();
        ((fdecl.value as MIRBody).vtypes as Map<string, string>).forEach((tkey, name) => {
            this.vtypes.set(name, this.typegen.getMIRType(tkey));
        });

        const restype = this.typegen.typeToSMTCategory(this.typegen.getMIRType(fdecl.declaredType));
        const decl = `(define-fun ${this.invokenameToSMT(fdkey)} () Result@${restype}`;
        const blocks = (fdecl.value as MIRBody).body;
        const body = this.generateBlockExps(blocks.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocks, undefined);
        return `${decl} \n${body.emit("  ")})`;
    }

    generateBuiltinBody(idecl: MIRInvokePrimitiveDecl, params: string[]): SMTExp {
        const rtype = this.typegen.getMIRType(idecl.resultType);

        let bodyres: SMTExp | undefined = undefined;
        let autowrap = true;
        switch (idecl.implkey) {
            case "list_size": {
                bodyres = new SMTValue(`(bsqlist@size ${params[0]})`);
                break;
            }
            case "list_unsafe_at": {
                bodyres = this.typegen.coerce(new SMTValue(`(select (bsqlist@entries ${params[0]}) ${params[1]})`), this.typegen.anyType, rtype);
                break;
            }
            case "list_unsafe_add": {
                const storeval = this.typegen.coerce(new SMTValue(params[1]), this.typegen.getMIRType(idecl.params[1].type), this.typegen.anyType).emit();
                const idx = `(bsqlist@size ${params[0]})`;
                bodyres = new SMTValue(`(cons@bsqlist (+ (bsqlist@size ${params[0]}) 1) (store (bsqlist@entries ${params[0]}) ${idx} ${storeval}))`);
                break;
            }
            case "list_unsafe_set": {
                const storeval = this.typegen.coerce(new SMTValue(params[2]), this.typegen.getMIRType(idecl.params[2].type), this.typegen.anyType).emit();
                bodyres = new SMTValue(`(cons@bsqlist (bsqlist@size ${params[0]}) (store (bsqlist@entries ${params[0]}) ${params[1]} ${storeval}))`);
                break;
            }
            case "list_destructive_add": {
                const storeval = this.typegen.coerce(new SMTValue(params[1]), this.typegen.getMIRType(idecl.params[1].type), this.typegen.anyType).emit();
                bodyres = new SMTValue(`(cons@bsqlist (+ (bsqlist@size ${params[0]}) 1) (store (bsqlist@entries ${params[0]}) (bsqlist@size ${params[0]}) ${storeval}))`);
                break;
            }
            case "keylist_cons": {
                bodyres = new SMTValue(`(cons@bsqkeylist ${params[0]} ${params[1]})`);
                break;
            }
            case "keylist_getkey": {
                bodyres = new SMTValue(`(bsqkeylist@key ${params[0]})`);
                break;
            }
            case "keylist_gettail": {
                bodyres = new SMTValue(`(bsqkeylist@tail ${params[0]})`);
                break;
            }
            case "set_size":
            case "map_size": {
                bodyres = new SMTValue(`(bsqkvcontainer@size ${params[0]})`);
                break;
            }
            case "set_has_key":
            case "map_has_key": {
                bodyres = new SMTValue(`(not (is-bsqterm@clear (select (bsqkvcontainer@entries ${params[0]}) ${params[1]})))`);
                break;
            }
            case "set_at_val":
            case "map_at_val": {
                bodyres = this.typegen.coerce(new SMTValue(`(select (bsqkvcontainer@entries ${params[0]}) ${params[1]})`), this.typegen.anyType, rtype);
                break;
            }
            case "set_get_keylist":
            case "map_get_keylist": {
                bodyres = new SMTValue(`(bsqkvcontainer@keylist ${params[0]})`);
                break;
            } 
            case "set_clear_val": 
            case "map_clear_val": {
                bodyres = new SMTValue(`(cons@bsqkvcontainer (- (bsqkvcontainer@size ${params[0]}) 1) ${params[2]} (store (bsqkvcontainer@entries ${params[0]}) ${params[1]} bsqterm@clear))`);
                break;
            }
            case "set_unsafe_update":  
            case "map_unsafe_update":
            case "set_destuctive_update":
            case "map_destuctive_update": {
                const storeval = this.typegen.coerce(new SMTValue(params[2]), this.typegen.getMIRType(idecl.params[2].type), this.typegen.anyType).emit();
                bodyres = new SMTValue(`(cons@bsqkvcontainer (bsqkvcontainer@size ${params[0]}) (bsqkvcontainer@keylist ${params[0]}) (store (bsqkvcontainer@entries ${params[0]}) ${params[1]} ${storeval}))`);
                break;
            }
            case "set_unsafe_add":  
            case "map_unsafe_add": 
            case "set_destuctive_add":
            case "map_destuctive_add": {
                const storeval = this.typegen.coerce(new SMTValue(params[2]), this.typegen.getMIRType(idecl.params[2].type), this.typegen.anyType).emit();
                bodyres = new SMTValue(`(cons@bsqkvcontainer (+ (bsqkvcontainer@size ${params[0]}) 1) ${params[3]} (store (bsqkvcontainer@entries ${params[0]}) ${params[1]} ${storeval}))`);
                break;
            }
            default: {
                bodyres = new SMTValue(`[Builtin not defined -- ${idecl.iname}]`);
                break;
            }
        }

        if(!autowrap) {
            return bodyres;
        }
        else {
            return new SMTValue(`(result_success@${this.typegen.typeToSMTCategory(rtype)} ${bodyres.emit()})`)
        }
    }
}

export {
    SMTBodyEmitter
};
