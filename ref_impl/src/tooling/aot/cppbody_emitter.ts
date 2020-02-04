//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIRInvokeDecl, MIRInvokeBodyDecl, MIRInvokePrimitiveDecl, MIRConstantDecl, MIRFieldDecl, MIREntityTypeDecl, MIRFunctionParameter, MIREntityType, MIRTupleType, MIRRecordType, MIRConceptType, MIREpemeralListType } from "../../compiler/mir_assembly";
import { CPPTypeEmitter } from "./cpptype_emitter";
import { MIRArgument, MIRRegisterArgument, MIRConstantNone, MIRConstantFalse, MIRConstantTrue, MIRConstantInt, MIRConstantArgument, MIRConstantString, MIROp, MIROpTag, MIRLoadConst, MIRAccessArgVariable, MIRAccessLocalVariable, MIRInvokeFixedFunction, MIRPrefixOp, MIRBinOp, MIRBinEq, MIRBinCmp, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRRegAssign, MIRTruthyConvert, MIRLogicStore, MIRVarStore, MIRReturnAssign, MIRDebug, MIRJump, MIRJumpCond, MIRJumpNone, MIRAbort, MIRBasicBlock, MIRPhi, MIRConstructorTuple, MIRConstructorRecord, MIRAccessFromIndex, MIRAccessFromProperty, MIRInvokeKey, MIRAccessConstantValue, MIRLoadFieldDefaultValue, MIRBody, MIRConstructorPrimary, MIRBodyKey, MIRAccessFromField, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionSingletons, MIRIsTypeOf, MIRProjectFromIndecies, MIRModifyWithIndecies, MIRStructuredExtendTuple, MIRProjectFromProperties, MIRModifyWithProperties, MIRStructuredExtendRecord, MIRResolvedTypeKey, MIRLoadConstTypedString, MIRConstructorEphemeralValueList, MIRProjectFromFields, MIRModifyWithFields, MIRStructuredExtendObject } from "../../compiler/mir_ops";
import { topologicalOrder } from "../../compiler/mir_info";
import { MIRKeyGenerator } from "../../compiler/mir_emitter";

import * as assert from "assert";

function NOT_IMPLEMENTED<T>(msg: string): T {
    throw new Error(`Not Implemented: ${msg}`);
}

function filenameClean(file: string): string {
    return file.replace(/[\\]/g, "/");
}

class CPPBodyEmitter {
    readonly assembly: MIRAssembly;
    readonly typegen: CPPTypeEmitter;
    
    readonly allPropertyNames: Set<string> = new Set<string>();
    readonly allConstStrings: Map<string, string> = new Map<string, string>();
    readonly allConstBigInts: Map<string, string> = new Map<string, string>();

    private currentFile: string = "[No File]";
    private currentRType: MIRType;

    private vtypes: Map<string, MIRType> = new Map<string, MIRType>();
    private generatedBlocks: Map<string, string[]> = new Map<string, string[]>();

    private subtypeOrderCtr = 0;
    subtypeFMap: Map<string, {order: number, decl: string}> = new Map<string, {order: number, decl: string}>();

    vfieldUpdates: { arg: MIRArgument, infertype: MIRType, fupds: [MIRFieldDecl, MIRArgument][], uname: string }[] = [];
    vobjmerges: { arg: MIRArgument, infertype: MIRType, merge: MIRArgument, infermergetype: MIRType, fieldResolves: [string, MIRFieldDecl][], mname: string }[] = [];

    constructor(assembly: MIRAssembly, typegen: CPPTypeEmitter) {
        this.assembly = assembly;
        this.typegen = typegen;
        
        this.currentRType = typegen.noneType;
    }

    labelToCpp(label: string): string {
        return label;
    }

    varNameToCppName(name: string): string {
        if (name === "this") {
            return this.typegen.mangleStringForCpp("$this");
        }
        else if (name === "_return_") {
            return "_return_";
        }
        else {
            return this.typegen.mangleStringForCpp(name);
        }
    }

    varToCppName(varg: MIRRegisterArgument): string {
        return this.varNameToCppName(varg.nameID);
    }

    invokenameToCPP(ivk: MIRInvokeKey): string {
        return this.typegen.mangleStringForCpp(ivk);
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

    generateConstantExp(cval: MIRConstantArgument, into: MIRType): string {
        if (cval instanceof MIRConstantNone) {
            return this.typegen.coerce("BSQ_VALUE_NONE", this.typegen.noneType, into);
        }
        else if (cval instanceof MIRConstantTrue) {
            return this.typegen.coerce("true", this.typegen.boolType, into);
        }
        else if (cval instanceof MIRConstantFalse) {
            return this.typegen.coerce("false", this.typegen.boolType, into);
        }
        else if (cval instanceof MIRConstantInt) {
            let bint = "";
            if (cval.value === "0") {
                bint = "BSQ_VALUE_0";
            }
            else if (cval.value === "1") {
                bint = "BSQ_VALUE_POS_1";
            }
            else if (cval.value === "-1") {
                bint = "BSQ_VALUE_NEG_1";
            }
            else {
                if(Number.isSafeInteger(Number.parseInt(cval.value))) {
                    bint = `BSQ_ENCODE_VALUE_TAGGED_INT(${cval.value})`;
                }
                else {
                    const sname = "BIGINT__" + this.allConstStrings.size;
                    if (!this.allConstBigInts.has(cval.value)) {
                        this.allConstBigInts.set(cval.value, sname);
                    }
        
                    bint = `(Runtime::${this.allConstBigInts.get(cval.value) as string})`;
                }
            }

            return this.typegen.coerce(bint, this.typegen.intType, into);
        }
        else {
            assert(cval instanceof MIRConstantString);

            const sval = (cval as MIRConstantString).value;
            const sname = "STR__" + this.allConstStrings.size;
            if (!this.allConstStrings.has(sval)) {
                this.allConstStrings.set(sval, sname);
            }

            const strval = `(&Runtime::${this.allConstStrings.get(sval) as string})`;
            return this.typegen.coerce(strval, this.typegen.stringType, into);
        }
    }

    argToCpp(arg: MIRArgument, into: MIRType): string {
        if (arg instanceof MIRRegisterArgument) {
            return this.typegen.coerce(this.varToCppName(arg), this.getArgType(arg), into);
        }
        else {
            return this.generateConstantExp(arg as MIRConstantArgument, into);
        }
    }

    generateTruthyConvert(arg: MIRArgument): string {
        const argtype = this.getArgType(arg);

        if (this.assembly.subtypeOf(argtype, this.typegen.noneType)) {
            return "false";
        }
        else if (this.assembly.subtypeOf(argtype, this.typegen.boolType)) {
            return this.argToCpp(arg, this.typegen.boolType);
        }
        else {
            return `BSQ_GET_VALUE_TRUTHY(${this.varToCppName(arg)})`;
        }
    }

    generateNoneCheck(arg: MIRArgument): string {
        const argtype = this.getArgType(arg);

        if (this.assembly.subtypeOf(argtype, this.typegen.noneType)) {
            return "true";
        }
        else if (!this.assembly.subtypeOf(this.typegen.noneType, argtype)) {
            return "false";
        }
        else {
            return `BSQ_IS_VALUE_NONE(${this.varToCppName(arg)})`;
        }
    }

    generateLoadConstTypedString(op: MIRLoadConstTypedString): string {
        const sname = "STR__" + this.allConstStrings.size;
        if (!this.allConstStrings.has(op.ivalue)) {
            this.allConstStrings.set(op.ivalue, sname);
        }
        const strval = `Runtime::${this.allConstStrings.get(op.ivalue) as string}`;

        const ttype = this.typegen.getMIRType(op.tkey);
        let opstrs: string[] = [];

        if(op.pfunckey !== undefined) {
            const chkexp = `${this.invokenameToCPP(op.pfunckey)}(${strval})`;
            if(this.typegen.assembly.subtypeOf(ttype, this.typegen.validatorType)) {
                opstrs.push(`if(!${chkexp}) { BSQ_ABORT("Failed string validation", "${filenameClean(this.currentFile)}", ${op.sinfo.line}); }`);
            }
            else {
                opstrs.push(`if(!${chkexp}.success) { BSQ_ABORT("Failed string validation", "${filenameClean(this.currentFile)}", ${op.sinfo.line}); }`);
            }
        }

        const scopevar = this.varNameToCppName("$scope$");
        opstrs.push(`${this.varToCppName(op.trgt)} =  BSQ_NEW_ADD_SCOPE(${scopevar}, BSQStringOf, ${strval}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(op.tskey)});`);

        return opstrs.join(" ");
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

    generateAccessConstantValue(cp: MIRAccessConstantValue): string {
        const cdecl = this.assembly.constantDecls.get(cp.ckey) as MIRConstantDecl;

        const top = CPPBodyEmitter.expBodyTrivialCheck(cdecl.value);
        if (top !== undefined) {
            const cvv = top as MIRLoadConst;
            return `${this.varToCppName(cp.trgt)} = ${this.generateConstantExp(cvv.src, this.getArgType(cvv.trgt))};`;
        }
        else {
            return `${this.varToCppName(cp.trgt)} = ${this.invokenameToCPP(cdecl.value.bkey)}();`;
        }
    }

    generateLoadFieldDefaultValue(ld: MIRLoadFieldDefaultValue): string {
        const fdecl = this.assembly.fieldDecls.get(ld.fkey) as MIRFieldDecl;

        const top = CPPBodyEmitter.expBodyTrivialCheck(fdecl.value as MIRBody);
        if (top !== undefined) {
            const cvv = top as MIRLoadConst;
            return `${this.varToCppName(ld.trgt)} = ${this.generateConstantExp(cvv.src, this.getArgType(cvv.trgt))};`;
        }
        else {
            return `${this.varToCppName(ld.trgt)} = ${this.invokenameToCPP((fdecl.value as MIRBody).bkey)}();`;
        }
    }

    generateMIRConstructorPrimary(cp: MIRConstructorPrimary): string {
        const ctype = this.assembly.entityDecls.get(cp.tkey) as MIREntityTypeDecl;
        let fvals = cp.args.map((arg, i) => {
            const ftype = this.typegen.getMIRType(ctype.fields[i].declaredType);
            return this.typegen.generateConstructorArgInc(ftype, this.argToCpp(arg, ftype));
        });

        const cppctype = this.typegen.getCPPTypeFor(this.typegen.getMIRType(cp.tkey), "base");
        const scopevar = this.varNameToCppName("$scope$");
        const cexp = `${this.varToCppName(cp.trgt)} = BSQ_NEW_ADD_SCOPE(${scopevar}, ${cppctype}${fvals.length !== 0 ? (", " + fvals.join(", ")) : ""});`;
        if (ctype.invariants.length === 0) {
            return cexp;
        }
        else {
            const testexp = `${this.typegen.mangleStringForCpp("invariant::" + cp.tkey)}(${this.varToCppName(cp.trgt)});`;
            return cexp + " " + testexp;
        }
    }

    generateMIRConstructorPrimaryCollectionEmpty(cpce: MIRConstructorPrimaryCollectionEmpty): string {
        const cpetype = this.typegen.getMIRType(cpce.tkey);
        const cppctype = this.typegen.getCPPTypeFor(cpetype, "base");

        const scopevar = this.varNameToCppName("$scope$");
        const conscall = `BSQ_NEW_ADD_SCOPE(${scopevar}, ${cppctype}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(cpce.tkey)})`;

        return `${this.varToCppName(cpce.trgt)} = ${conscall};`;
    }

    generateMIRConstructorPrimaryCollectionSingletons(cpcs: MIRConstructorPrimaryCollectionSingletons): string {
        const cpcstype = this.typegen.getMIRType(cpcs.tkey);
        const cppctype = this.typegen.getCPPTypeFor(cpcstype, "base");

        let conscall = "";
        const scopevar = this.varNameToCppName("$scope$");
        if (this.typegen.typecheckIsName(cpcstype, /NSCore::List<.*>/)) {
            const oftype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
            const cvals = cpcs.args.map((arg) => {
                return this.typegen.generateConstructorArgInc(oftype, this.argToCpp(arg, oftype));
            });

            conscall = `${cppctype}::createFromSingle(${scopevar}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(cpcs.tkey)}, ${cvals.length}, ${cvals.join(", ")})`;
        }
        else if (this.typegen.typecheckIsName(cpcstype, /NSCore::Set<.*>/)) {
            const oftype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
            const cvals = cpcs.args.map((arg) => {
                return this.typegen.generateConstructorArgInc(oftype, this.argToCpp(arg, oftype));
            });

            conscall = `${cppctype}::createFromSingle(${scopevar}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(cpcs.tkey)}, ${cvals.length}, ${cvals.join(", ")})`;
        }
        else {
            const ktype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("K") as MIRType;
            const vtype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("V") as MIRType;
            const entrytype = [...this.typegen.assembly.entityDecls].find((edecl) => edecl[1].ns === "NSCore" && edecl[1].name === "MapEntry" && (edecl[1].terms.get("K") as MIRType).trkey === ktype.trkey && (edecl[1].terms.get("V") as MIRType).trkey === vtype.trkey);

            const oftype = this.assembly.typeMap.get((entrytype as [string, MIREntityTypeDecl])[0]) as MIRType;
            const cvals = cpcs.args.map((arg) => {
                return this.typegen.generateConstructorArgInc(oftype, this.argToCpp(arg, oftype));
            });

            conscall = `${cppctype}::createFromSingle(${scopevar}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(cpcs.tkey)}, ${cvals.length}, ${cvals.join(", ")})`;
        }

        return `${this.varToCppName(cpcs.trgt)} = ${conscall};`;
    }

    generateMIRConstructorTuple(op: MIRConstructorTuple): string {
        const args = op.args.map((arg) => this.argToCpp(arg, this.typegen.anyType));

        if(args.length === 0) {
            return `${this.varToCppName(op.trgt)} = BSQTuple::_empty;`;
        }
        else {
            const scopevar = this.varNameToCppName("$scope$");
            const iflag = this.typegen.generateInitialDataKindFlag(this.typegen.getMIRType(op.resultTupleType));
            return `${this.varToCppName(op.trgt)} = BSQTuple::createFromSingle(${scopevar}, ${iflag}, ${args.length}, ${args.join(", ")});`;
        }
    }

    generateMIRConstructorRecord(op: MIRConstructorRecord): string {
        const args = op.args.map((arg) => `std::make_pair(MIRPropertyEnum::${arg[0]}, ${this.argToCpp(arg[1], this.typegen.anyType)})`);

        if(args.length === 0) {
            return `${this.varToCppName(op.trgt)} = BSQRecord::_empty;`;
        }
        else {
            const scopevar = this.varNameToCppName("$scope$");
            const iflag = this.typegen.generateInitialDataKindFlag(this.typegen.getMIRType(op.resultRecordType));
            return `${this.varToCppName(op.trgt)} = BSQRecord::createFromSingle(${scopevar}, ${iflag}, ${args.length}, ${args.join(", ")});`;
        }
    }

    generateMIRConstructorEphemeralValueList(op: MIRConstructorEphemeralValueList): string {
        const etype = this.typegen.getMIRType(op.resultEphemeralListType).options[0] as MIREpemeralListType;

        let args: string[] = [];
        for(let i = 0; i < op.args.length; ++i) {
            args.push(this.argToCpp(op.args[i], etype.entries[i]));
        }

        return `${this.varToCppName(op.trgt)} = ${this.typegen.mangleStringForCpp(etype.trkey)}(${args.join(", ")});`;
    }

    generateMIRAccessFromIndexExpression(arg: MIRArgument, idx: number, resultAccessType: MIRType): string {
        const tuptype = this.getArgType(arg);
        const hasidx = this.typegen.tupleHasIndex(tuptype, idx);
    
        if(hasidx === "no") {
            return `${this.typegen.coerce("BSQ_VALUE_NONE", this.typegen.noneType, resultAccessType)}`;
        }
        else {
            const select = `BSQ_GET_VALUE_PTR(${this.varToCppName(arg)}, BSQTuple)->atFixed(${idx})`
            return `${this.typegen.coerce(select, this.typegen.anyType, resultAccessType)}`;
        }
    }

    generateMIRProjectFromIndecies(op: MIRProjectFromIndecies, resultAccessType: MIRType): string {
        const intotypes = this.typegen.typecheckEphemeral(resultAccessType) ? (resultAccessType.options[0] as MIREpemeralListType).entries : [];
        let vals: string[] = [];

        for (let i = 0; i < op.indecies.length; ++i) {
            vals.push(this.generateMIRAccessFromIndexExpression(op.arg, op.indecies[i], intotypes[i] || this.typegen.anyType));
        }

        if (this.typegen.typecheckEphemeral(resultAccessType)) {
            return `${this.varToCppName(op.trgt)} = ${this.typegen.mangleStringForCpp(resultAccessType.trkey)}(${vals.join(", ")});`;
        }
        else {
            const scopevar = this.varNameToCppName("$scope$");
            const iflag = this.typegen.generateInitialDataKindFlag(resultAccessType);
            return `${this.varToCppName(op.trgt)} = BSQTuple::createFromSingle(${scopevar}, ${iflag}, ${vals.length}, ${vals.join(", ")});`;
        }
    }

    generateMIRModifyWithIndecies(op: MIRModifyWithIndecies, resultTupleType: MIRType): string {
        const updmax = Math.max(...op.updates.map((upd) => upd[0] + 1));

        let cvals: string[] = [];
        for (let i = 0; i < updmax; ++i) {
            const upd = op.updates.find((update) => update[0] === i);
            if (upd !== undefined) {
                cvals.push(this.argToCpp(upd[1], this.typegen.anyType));
            }
            else {
                cvals.push(this.generateMIRAccessFromIndexExpression(op.arg, i, this.typegen.anyType));
            }
        }

        const rmax = this.typegen.getMaxTupleLength(resultTupleType);
        for (let i = updmax; i < rmax; ++i) {
            //may put none in the constructor list but ok since we note correct length and will ignore these if extranious
            cvals.push(this.generateMIRAccessFromIndexExpression(op.arg, i, this.typegen.anyType));
        }

        const scopevar = this.varNameToCppName("$scope$");
        const iflag = this.typegen.generateInitialDataKindFlag(resultTupleType);
        const realsize = `std::min(${updmax}, BSQ_GET_VALUE_PTR(${this.varToCppName(op.arg)}, BSQTuple)->entries.size())`;
        return `${this.varToCppName(op.trgt)} = BSQTuple::createFromSingle(${scopevar}, ${iflag}, ${realsize}, ${cvals.join(", ")});`; 
    }

    generateMIRStructuredExtendTuple(op: MIRStructuredExtendTuple, resultTupleType: MIRType): string {
         //this is the exact number of indecies in arg -- see typecheck
         const btuple = this.typegen.getMaxTupleLength(this.typegen.getMIRType(op.argInferType));

        let cvals: string[] = [];
        for (let i = 0; i < btuple; ++i) {
            cvals.push(this.generateMIRAccessFromIndexExpression(op.arg, i, this.typegen.anyType));
        }

        const rmax = this.typegen.getMaxTupleLength(resultTupleType);
        for (let i = btuple; i < rmax; ++i) {
            //may put none in the constructor list but ok since we note correct length and will ignore these if extranious
            cvals.push(this.generateMIRAccessFromIndexExpression(op.update, i, this.typegen.anyType));
        }

        const scopevar = this.varNameToCppName("$scope$");
        const iflag = this.typegen.generateInitialDataKindFlag(resultTupleType);
        const realsize = `BSQ_GET_VALUE_PTR(${this.varToCppName(op.arg)}, BSQTuple)->entries.size() + BSQ_GET_VALUE_PTR(${this.varToCppName(op.update)}, BSQTuple)->entries.size()`;
        return `${this.varToCppName(op.trgt)} = BSQTuple::createFromSingle(${scopevar}, ${iflag}, ${realsize}, ${cvals.join(", ")});`; 
    }

    generateMIRAccessFromPropertyExpression(arg: MIRArgument, property: string, resultAccessType: MIRType): string {
        const rectype = this.getArgType(arg);
        const hasproperty = this.typegen.recordHasField(rectype, property);
    
        if(hasproperty === "no") {
            return `${this.typegen.coerce("BSQ_VALUE_NONE", this.typegen.noneType, resultAccessType)}`;
        }
        else {
            const select = `BSQ_GET_VALUE_PTR(${this.varToCppName(arg)}, BSQRecord)->atFixed(MIRPropertyEnum::${property})`
            return `${this.typegen.coerce(select, this.typegen.anyType, resultAccessType)}`;
        }
    }

    generateMIRProjectFromProperties(op: MIRProjectFromProperties, resultAccessType: MIRType): string {
        const intotypes = this.typegen.typecheckEphemeral(resultAccessType) ? (resultAccessType.options[0] as MIREpemeralListType).entries : [];
        let vals: string[] = [];

        for (let i = 0; i < op.properties.length; ++i) {
            vals.push(this.generateMIRAccessFromPropertyExpression(op.arg, op.properties[i], intotypes[i] || this.typegen.anyType));
        }

        if (this.typegen.typecheckEphemeral(resultAccessType)) {
            return `${this.varToCppName(op.trgt)} = ${this.typegen.mangleStringForCpp(resultAccessType.trkey)}(${vals.join(", ")});`;
        }
        else {
            const rargs: string[] = [];
            for(let i = 0; i < op.properties.length; ++i) {
                rargs.push(`std::make_tuple<MIRRecordEnum, Value>(MIRRecordEnum::${op.properties[i]}, ${vals[i]})`);
            }

            const scopevar = this.varNameToCppName("$scope$");
            const iflag = this.typegen.generateInitialDataKindFlag(resultAccessType);
            return `${this.varToCppName(op.trgt)} = BSQRecord::createFromSingle(${scopevar}, ${iflag}, ${rargs.length}, ${rargs.join(", ")});`;
        }
    }

    generateMIRModifyWithProperties(op: MIRModifyWithProperties, resultRecordType: MIRType): string {
        const pmax = this.typegen.getMaxPropertySet(resultRecordType);

        let cvals: string[] = [];
        for (let i = 0; i < pmax.length; ++i) {
            const pname = pmax[i];
            const upd = op.updates.find((update) => update[0] === pname);
            if (upd !== undefined) {
                cvals.push(`std::make_pair<MIRRecordEnum, Value>(MIRRecordEnum::${pname}, ${this.argToCpp(upd[1], this.typegen.anyType)})`);
            }
        }

        const scopevar = this.varNameToCppName("$scope$");
        const iflag = this.typegen.generateInitialDataKindFlag(resultRecordType);
        return `${this.varToCppName(op.trgt)} = BSQRecord::createFromUpdate(${scopevar}, BSQ_GET_VALUE_PTR(${this.varToCppName(op.arg)}, BSQRecord), ${iflag}, ${cvals.length}, ${cvals.join(", ")});`;
    }

    generateMIRStructuredExtendRecord(op: MIRStructuredExtendRecord, resultRecordType: MIRType): string {
        const rprops = this.typegen.getMaxPropertySet(resultRecordType);
        const mtype = this.typegen.getMIRType(op.updateInferType);

        let cvals: string[] = [];
        for(let i = 0; i < rprops.length; ++i) {
            const pname = rprops[i];
            const uhas = this.typegen.recordHasField(mtype, pname);
            if(uhas === "no") {
                //nothing to do
            }
            else if (uhas === "yes") {
                cvals.push(`std::make_pair<MIRRecordEnum, Value>(MIRRecordEnum::${pname}, ${this.generateMIRAccessFromPropertyExpression(op.update, pname, this.typegen.anyType)})`);
            }
            else {
                const check = `BSQ_GET_VALUE_PTR(${this.varToCppName(op.update)}, BSQRecord)->hasProperty(MIRPropertyEnum::${pname})`;
                cvals.push(`${check} ? ${this.generateMIRAccessFromPropertyExpression(op.update, pname, this.typegen.anyType)}) : ${this.generateMIRAccessFromPropertyExpression(op.arg, pname, this.typegen.anyType)})`);
            }
        }

        const scopevar = this.varNameToCppName("$scope$");
        const iflag = this.typegen.generateInitialDataKindFlag(resultRecordType);
        return `${this.varToCppName(op.trgt)} = BSQRecord::createFromUpdate(${scopevar}, BSQ_GET_VALUE_PTR(${this.varToCppName(op.arg)}, BSQRecord), ${iflag}, ${cvals.length}, ${cvals.join(", ")});`;
    }

    generateMIRAccessFromField(op: MIRAccessFromField, resultAccessType: MIRType): string {
        const inferargtype = this.typegen.getMIRType(op.argInferType);
        const fdecl = this.assembly.fieldDecls.get(op.field) as MIRFieldDecl;
        const ftype = this.typegen.getMIRType(fdecl.declaredType);

        if (this.typegen.typecheckUEntity(inferargtype)) {
            const access = `${this.argToCpp(op.arg, inferargtype)}->${this.typegen.mangleStringForCpp(op.field)}`;
            return `${this.varToCppName(op.trgt)} = ${this.typegen.coerce(access, ftype, resultAccessType)};`;
        }
        else {
            const access = `BSQ_GET_VALUE_PTR(${this.argToCpp(op.arg, inferargtype)}, BSQObject)->get$${this.typegen.mangleStringForCpp(op.field)}()`;
            return `${this.varToCppName(op.trgt)} = ${this.typegen.coerce(access, ftype, resultAccessType)};`;
        }
    }

    generateMIRProjectFromFields(op: MIRProjectFromFields): string {
        const inferargtype = this.typegen.getMIRType(op.argInferType);

        let cvals: string[] = [];
        op.fields.map((f) => {
            const fdecl = this.assembly.fieldDecls.get(f) as MIRFieldDecl;
            const ftype = this.typegen.getMIRType(fdecl.declaredType);

            if (this.typegen.typecheckUEntity(inferargtype)) {
                const access = `${this.argToCpp(op.arg, inferargtype)}->${this.typegen.mangleStringForCpp(fdecl.fkey)}`;
                cvals.push(`std::make_pair<MIRRecordEnum, Value>(MIRRecordEnum::${fdecl.name}, ${this.typegen.coerce(access, ftype, this.typegen.anyType)})`);
            }
            else {
                const access = `BSQ_GET_VALUE_PTR(${this.argToCpp(op.arg, inferargtype)}, BSQObject)->get$${this.typegen.mangleStringForCpp(fdecl.fkey)}()`;
                cvals.push(`std::make_pair<MIRRecordEnum, Value>(MIRRecordEnum::${fdecl.name}, ${this.typegen.coerce(access, ftype, this.typegen.anyType)})`);
            }
        });

        const scopevar = this.varNameToCppName("$scope$");
        const iflag = this.typegen.generateInitialDataKindFlag(this.typegen.getMIRType(op.resultProjectType));
        return `${this.varToCppName(op.trgt)} = BSQRecord::createFromSingle(${scopevar}, ${iflag}, ${cvals.length}, ${cvals.join(", ")});`;
    }

    generateVFieldUpdates(arg: MIRArgument, infertype: MIRType, fupds: [MIRFieldDecl, MIRArgument][]): string {
        const upnames = fupds.map((fud) => `${fud[0].fkey}->${this.getArgType(fud[1])}`);
        const uname = `update_${upnames.sort().join("*")}_in_${infertype.trkey}`;
        let decl = this.vfieldUpdates.find((lookup) => lookup.uname === uname);
        if(decl === undefined) {
            this.vfieldUpdates.push({ arg: arg, infertype: infertype, fupds: fupds, uname: uname });
        }

        return `${this.typegen.mangleStringForCpp(uname)}(${this.argToCpp(arg, infertype)}, ${fupds.map((upd) => this.argToCpp(upd[1], this.getArgType(upd[1]))).join(", ")})`;
    }

    generateMIRModifyWithFields(op: MIRModifyWithFields): string {
        const inferargtype = this.typegen.getMIRType(op.argInferType);
        
        if (this.typegen.typecheckUEntity(inferargtype)) {
            const ekey = this.typegen.getEntityEKey(inferargtype);
            const utype = this.typegen.assembly.entityDecls.get(ekey) as MIREntityTypeDecl;
            let cvals: [string, MIRType][] = [];
            for (let i = 0; i < utype.fields.length; ++i) {
                const fdecl = utype.fields[i];
                const ftype = this.typegen.getMIRType(fdecl.declaredType);

                const upd = op.updates.find((update) => update[0] == fdecl.fkey);
                if(upd !== undefined) {
                    cvals.push([this.argToCpp(upd[1], ftype), ftype]);
                }
                else {
                    cvals.push([`${this.argToCpp(op.arg, inferargtype)}->${this.typegen.mangleStringForCpp(fdecl.fkey)}`, ftype]);
                }
            }

            let fvals = cvals.map((val) => {
                return this.typegen.generateConstructorArgInc(val[1], val[0]);
            });
    
            const cppctype = this.typegen.getCPPTypeFor(inferargtype, "base");
            const scopevar = this.varNameToCppName("$scope$");
            const cexp = `${this.varToCppName(op.trgt)} = BSQ_NEW_ADD_SCOPE(${scopevar}, ${cppctype}${fvals.length !== 0 ? (", " + fvals.join(", ")) : ""});`;
            if (utype.invariants.length === 0) {
                return cexp;
            }
            else {
                const testexp = `${this.typegen.mangleStringForCpp("invariant::" + ekey)}(${this.varToCppName(op.trgt)});`;
                return cexp + " " + testexp;
            }
        }
        else {
            const access = this.generateVFieldUpdates(op.arg, inferargtype, op.updates.map((upd) => [this.assembly.fieldDecls.get(upd[0]) as MIRFieldDecl, upd[1]]));
            return `${this.varToCppName(op.trgt)} = ${access};`;
        }
    }

    generateVFieldExtend(arg: MIRArgument, infertype: MIRType, merge: MIRArgument, infermerge: MIRType, fieldResolves: [string, MIRFieldDecl][]): string {
        const upnames = fieldResolves.map((fr) => `${fr[0]}->${fr[1].fkey}`);
        const mname = `merge_${infertype.trkey}_${upnames.join("*")}_with_${infermerge.trkey}`;
        let decl = this.vobjmerges.find((lookup) => lookup.mname === mname);
        if(decl === undefined) {
            this.vobjmerges.push({ arg: arg, infertype: infertype, merge: merge, infermergetype: infermerge, fieldResolves: fieldResolves, mname: mname });
        }

        return `${this.typegen.mangleStringForCpp(mname)}(${this.argToCpp(arg, infertype)}, ${this.argToCpp(merge, infermerge)})`;
    }

    generateMIRStructuredExtendObject(op: MIRStructuredExtendObject): string {
        const inferargtype = this.typegen.getMIRType(op.argInferType);
        const mergeargtype = this.typegen.getMIRType(op.updateInferType);
        
        if (this.typegen.typecheckUEntity(inferargtype)) {
            const ekey = this.typegen.getEntityEKey(inferargtype);
            const utype = this.typegen.assembly.entityDecls.get(ekey) as MIREntityTypeDecl;
            let cvals: [string, MIRType][] = [];
            for (let i = 0; i < utype.fields.length; ++i) {
                const fdecl = utype.fields[i];
                const ftype = this.typegen.getMIRType(fdecl.declaredType);

                const fp = op.fieldResolves.find((tfp) => tfp[1] === fdecl.fkey);
                const faccess = [`${this.argToCpp(op.arg, inferargtype)}->${this.typegen.mangleStringForCpp(fdecl.fkey)}`, ftype] as [string, MIRType];
                if(fp === undefined) {
                    cvals.push(faccess);
                }
                else {
                    const hasp = this.typegen.recordHasField(mergeargtype, fp[0]);
                    if(hasp === "no") {
                        cvals.push(faccess);
                    }
                    else if (hasp === "yes") {
                        cvals.push([this.generateMIRAccessFromPropertyExpression(op.arg, fp[0], ftype), ftype]);
                    }
                    else {
                        const check = `BSQ_GET_VALUE_PTR(${this.varToCppName(op.update)}, BSQRecord)->hasProperty(MIRPropertyEnum::${fp[0]})`;
                        const update = `(${check} ? ${this.generateMIRAccessFromPropertyExpression(op.update, fp[0], ftype)}) : ${faccess})`;

                        cvals.push([update, ftype]);
                    }
                }
            }

            let fvals = cvals.map((val) => {
                return this.typegen.generateConstructorArgInc(val[1], val[0]);
            });
    
            const cppctype = this.typegen.getCPPTypeFor(inferargtype, "base");
            const scopevar = this.varNameToCppName("$scope$");
            const cexp = `${this.varToCppName(op.trgt)} = BSQ_NEW_ADD_SCOPE(${scopevar}, ${cppctype}${fvals.length !== 0 ? (", " + fvals.join(", ")) : ""});`;
            if (utype.invariants.length === 0) {
                return cexp;
            }
            else {
                const testexp = `${this.typegen.mangleStringForCpp("invariant::" + ekey)}(${this.varToCppName(op.trgt)});`;
                return cexp + " " + testexp;
            }
        }
        else {
            const access = this.generateVFieldExtend(op.arg, inferargtype, op.update, mergeargtype, op.fieldResolves.map((fr) => [fr[0], this.assembly.fieldDecls.get(fr[1]) as MIRFieldDecl]));
            return `${this.varToCppName(op.trgt)} = ${access};`;
        }
    }

    generateMIRInvokeFixedFunction(ivop: MIRInvokeFixedFunction): string {
        let vals: string[] = [];
        const idecl = (this.assembly.invokeDecls.get(ivop.mkey) || this.assembly.primitiveInvokeDecls.get(ivop.mkey)) as MIRInvokeDecl;

        for (let i = 0; i < ivop.args.length; ++i) {
            vals.push(this.argToCpp(ivop.args[i], this.typegen.getMIRType(idecl.params[i].type)));
        }

        const rtype = this.typegen.getMIRType(ivop.resultType);
        if (this.typegen.maybeRefableCountableType(rtype)) {
            vals.push(this.varNameToCppName("$scope$"));
        }

        return `${this.varToCppName(ivop.trgt)} = ${this.invokenameToCPP(ivop.mkey)}(${vals.join(", ")});`;
    }

    generateEquals(op: string, lhsinfertype: MIRType, lhs: MIRArgument, rhsinfertype: MIRType, rhs: MIRArgument, isstrict: boolean): string {
        let coreop = "";
        if (isstrict) {
            coreop = `EqualFunctor_${this.typegen.getCPPTypeFor(lhsinfertype, "base")}{}(${this.argToCpp(lhs, lhsinfertype)} ${op} ${this.argToCpp(rhs, rhsinfertype)})`;
        }
        else {
            coreop = `BSQIndexableEqual{}(${this.argToCpp(lhs, this.typegen.keyType)}, ${this.argToCpp(rhs, this.typegen.keyType)})`;
        }

        return op === "!=" ? `!${coreop}` : coreop; 
    }

    generateCompare(op: string, lhsinfertype: MIRType, lhs: MIRArgument, rhsinfertype: MIRType, rhs: MIRArgument): string {
        if (lhsinfertype.trkey === "NSCore::Int" && rhsinfertype.trkey === "NSCore::Int") {
            return `(${this.argToCpp(lhs, lhsinfertype)} ${op} ${this.argToCpp(rhs, rhsinfertype)})`;
        }
        else {
            return NOT_IMPLEMENTED<string>("compare string");
        }
    }

    generateSubtypeTupleCheck(argv: string, argtype: MIRType, oftype: MIRTupleType): string {
        const subtypesig = `bool subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}(const BSQTuple* atuple)`;

        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            let checks: string[] = [];

            checks.push(`(atuple->entries.size() <= ${oftype.entries.length})`);

            //do all the checks that argtype satisfies all the requirements of oftype -- maybe a bit inefficiently
            for (let i = 0; i < oftype.entries.length; ++i) {
                const chk = this.generateTypeCheck(`atuple->atFixed(${i})`, this.typegen.anyType, this.typegen.anyType, oftype.entries[i].type);

                if(oftype.entries[i].isOptional) {
                    checks.push(`(!atuple->hasIndex(${i}) || ${chk})`);
                }
                else {
                    checks.push(`atuple->hasIndex(${i})`);
                    checks.push(chk);
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
                    op = `(${checks.join(" && ")})`;
                }
            }

            const decl = subtypesig
            + "\n{\n"
            + `    return ${op};\n`
            + `}\n`;

            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }

        return `subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}(${argv})`;
    }

    generateSubtypeRecordCheck(argv: string, argtype: MIRType, oftype: MIRRecordType): string {
        const subtypesig = `bool subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}(const BSQRecord* arecord)`;

        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            let checks: string[] = [];

            //do all the checks that argtype satisfies all the requirements of oftype -- maybe a bit inefficiently
            for (let i = 0; i < oftype.entries.length; ++i) {
                const pname = oftype.entries[i].name;
                const chk = this.generateTypeCheck(`arecord->atFixed(MIRPropertyEnum::${pname})`, this.typegen.anyType, this.typegen.anyType, oftype.entries[i].type);

                if (oftype.entries[i].isOptional) {
                    checks.push(`(!arecord->hasProperty(MIRPropertyEnum::${pname}) || ${chk})`);
                }
                else {
                    checks.push(`arecord->hasProperty(MIRPropertyEnum::${pname})`);
                    checks.push(chk);
                }
            }

            //do checks that argtype doesn't have any other properties
            if (this.typegen.typecheckRecord(argtype)) {
                const allprops = this.typegen.getMaxPropertySet(argtype);

                for (let i = 0; i < allprops.length; ++i) {
                    const pname = allprops[i];
                    if (oftype.entries.find((entry) => entry.name === pname) === undefined) {
                        checks.push(`!arecord->hasProperty(MIRPropertyEnum::${pname})`);
                    }
                }
            }
            else {
                const pprops = oftype.entries.map((entry) => `MIRPropertyEnum::${entry.name}`);
                checks.push(`arecord->checkPropertySet(${oftype.entries.length}${oftype.entries.length !== 0 ? ", " : ""} ${pprops.join(", ")})`);
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
                    op = `(${checks.join(" && ")})`;
                }
            }

            const decl = subtypesig
            + "\n{\n"
            + `    return ${op};\n`
            + `}\n`;

            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }

        return `subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}(${argv})`;
    }

    generateSubtypeConceptCheck(argv: string, argtype: MIRType, oftype: MIRConceptType): string {
        const subtypesig = `bool subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}(Value val)`;

        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            const moftype = this.typegen.getMIRType(oftype.trkey);

            let getenum = `auto nenum = getNominalTypeOf_Value(${argv});`;

            let tchk = "[INVALID]";
            if(this.typegen.assembly.subtypeOf(this.typegen.tupleType, moftype)) {
                tchk = "true";
            }
            else if (this.typegen.assembly.subtypeOf(moftype, this.typegen.apiType)) {
                tchk = `((BSQ_GET_VALUE_PTR(${argv}, BSQTuple)->flag & DATA_KIND_API_FLAG) != DATA_KIND_CLEAR_FLAG)`;
            }
            else if(this.typegen.assembly.subtypeOf(moftype, this.typegen.podType)) {
                tchk = `((BSQ_GET_VALUE_PTR(${argv}, BSQTuple)->flag & DATA_KIND_POD_FLAG) != DATA_KIND_CLEAR_FLAG)`;
            }
            else {
                tchk = "false";
            }
            let chktuple = `if (nenum == MIRNominalTypeEnum_Tuple) { return ${tchk}; }`

            let rchk = "[INVALID]";
            if(this.typegen.assembly.subtypeOf(this.typegen.recordType, moftype)) {
                rchk = "true";
            }
            else if (this.typegen.assembly.subtypeOf(moftype, this.typegen.apiType)) {
                rchk = `((BSQ_GET_VALUE_PTR(${argv}, BSQRecord)->flag & DATA_KIND_API_FLAG) != DATA_KIND_CLEAR_FLAG))`;
            }
            else if(this.typegen.assembly.subtypeOf(moftype, this.typegen.podType)) {
                rchk = `((BSQ_GET_VALUE_PTR(${argv}, BSQRecord)->flag & DATA_KIND_POD_FLAG) != DATA_KIND_CLEAR_FLAG)`;
            }
            else {
                rchk = "false";
            }
            let chkrecord = `else if (nenum == MIRNominalTypeEnum_Record) { return ${rchk}; }`

            
            let fchk = this.generateConceptArrayLookup(`getNominalTypeOf_Value(${argv})`, oftype);
            let chkrest = `else { return ${fchk} }`;

            const decl = subtypesig
            + "\n{\n"
            + `    ${getenum}\n`
            + `    ${chktuple}\n`
            + `    ${chkrecord}\n`
            + `    ${chkrest}\n`
            + `}\n`;

            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }

        return `subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}(${argv})`;
    }

    generateFastTupleTypeCheck(arg: string, argtype: MIRType, oftype: MIRTupleType): string {
        if (this.typegen.typecheckTuple(argtype)) {
            return this.generateSubtypeTupleCheck(arg, argtype, oftype);
        }
        else {
            const tsc = this.generateSubtypeTupleCheck(`BSQ_GET_VALUE_PTR(${arg}, BSQTuple)`, argtype, oftype);
            return `(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQTuple*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr && ${tsc})`
        }
    }

    generateFastRecordTypeCheck(arg: string, argtype: MIRType, oftype: MIRRecordType): string {
        if (this.typegen.typecheckRecord(argtype)) {
            return this.generateSubtypeRecordCheck(arg, argtype, oftype);
        }
        else {
            const tsc = this.generateSubtypeRecordCheck(`BSQ_GET_VALUE_PTR(${arg}, BSQRecord)`, argtype, oftype);
            return `(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQRecord*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr && ${tsc})`
        }
    }

    generateFastEntityTypeCheck(arg: string, argtype: MIRType, oftype: MIREntityType): string {
        if (this.typegen.typecheckIsName(argtype, /^NSCore::Bool$/) || this.typegen.typecheckIsName(argtype, /^NSCore::Int$/) || this.typegen.typecheckIsName(argtype, /^NSCore::String$/)) {
            return oftype.ekey === argtype.trkey ? "true" : "false";
        }
        else if (this.typegen.typecheckIsName(argtype, /^NSCore::ValidatedString<.*>$/) || this.typegen.typecheckIsName(argtype, /^NSCore::StringOf<.*>$/)) {
            return oftype.ekey === argtype.trkey ? "true" : "false";
        }
        else if (this.typegen.typecheckIsName(argtype, /^NSCore::GUID$/) || this.typegen.typecheckIsName(argtype, /^NSCore::EventTime$/)
            || this.typegen.typecheckIsName(argtype, /^NSCore::DataHash$/) || this.typegen.typecheckIsName(argtype, /^NSCore::CryptoHash$/)) {
            return oftype.ekey === argtype.trkey ? "true" : "false";
        }
        else if (this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.enumtype) || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.idkeytype)
            || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.guididkeytype) || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.eventtimeidkeytype)
            || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.datahashidkeytype) || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.cryptohashidkeytype)) {
            return oftype.ekey === argtype.trkey ? "true" : "false";
        }
        else {
            if(this.typegen.typecheckAllKeys(argtype)) {
                return `(getNominalTypeOf_KeyValue(${arg}) == MIRNominalTypeEnum_${this.typegen.mangleStringForCpp(oftype.ekey)})`;
            }
            else if (this.typegen.typecheckIsName(argtype, /^NSCore::Buffer<.*>$/)) {
                return oftype.ekey === argtype.trkey ? "true" : "false";
            }
            else if (this.typegen.typecheckIsName(argtype, /^NSCore::ISOTime$/) || this.typegen.typecheckIsName(argtype, /^NSCore::Regex$/)) {
                return oftype.ekey === argtype.trkey ? "true" : "false";
            }
            else if (this.typegen.typecheckTuple(argtype) || this.typegen.typecheckRecord(argtype)) {
                return "false";
            }
            else if(this.typegen.typecheckUEntity(argtype)) {
                return oftype.ekey === argtype.trkey ? "true" : "false";
            }
            else {
                return `(getNominalTypeOf_Value(${arg}) == MIRNominalTypeEnum_${this.typegen.mangleStringForCpp(oftype.ekey)})`;
            }
        }
    }

    generateConceptArrayLookup(access: string, oftype: MIRConceptType): string {
        const lookups = oftype.ckeys.map((ckey) => {
            const sizestr = this.typegen.getSubtypesArrayCount(ckey);
            const arraystr = `MIRConceptSubtypeArray__${this.typegen.mangleStringForCpp(ckey)}`;

            return `BSQObject::checkSubtype<${sizestr}>(${access}, ${arraystr})`;
        });

        if(lookups.length === 1) {
            return lookups[0];
        }
        else {
            return lookups.join(" && ");
        }
    }

    generateFastConceptTypeCheck(arg: string, argtype: MIRType, oftype: MIRConceptType): string {
        if(oftype.trkey === "NSCore::Any") {
            return "true";
        }

        if(oftype.trkey === "NSCore::Some") {
            return !this.typegen.assembly.subtypeOf(this.typegen.noneType, argtype) ? "true" : `BSQ_IS_VALUE_NONNONE(${arg})`;
        }

        const moftype = this.typegen.getMIRType(oftype.trkey);
        if (this.typegen.typecheckIsName(argtype, /^NSCore::Bool$/) || this.typegen.typecheckIsName(argtype, /^NSCore::Int$/) || this.typegen.typecheckIsName(argtype, /^NSCore::String$/)) {
            return this.typegen.assembly.subtypeOf(argtype, moftype) ? "true" : "false";
        }
        else if (this.typegen.typecheckIsName(argtype, /^NSCore::ValidatedString<.*>$/) || this.typegen.typecheckIsName(argtype, /^NSCore::StringOf<.*>$/)) {
            return this.typegen.assembly.subtypeOf(argtype, moftype) ? "true" : "false";
        }
        else if (this.typegen.typecheckIsName(argtype, /^NSCore::GUID$/) || this.typegen.typecheckIsName(argtype, /^NSCore::EventTime$/)
            || this.typegen.typecheckIsName(argtype, /^NSCore::DataHash$/) || this.typegen.typecheckIsName(argtype, /^NSCore::CryptoHash$/)) {
            return this.typegen.assembly.subtypeOf(argtype, moftype) ? "true" : "false";
        }
        else if (this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.enumtype) || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.idkeytype)
            || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.guididkeytype) || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.eventtimeidkeytype)
            || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.datahashidkeytype) || this.typegen.typecheckEntityAndProvidesName(argtype, this.typegen.cryptohashidkeytype)) {
            return this.typegen.assembly.subtypeOf(argtype, moftype) ? "true" : "false";
        }
        else {
            if(this.typegen.typecheckAllKeys(argtype)) {
                return this.generateConceptArrayLookup(`getNominalTypeOf_KeyValue(${arg})`, oftype);
            }
            else if (this.typegen.typecheckIsName(argtype, /^NSCore::Buffer<.*>$/)) {
                return this.typegen.assembly.subtypeOf(argtype, moftype) ? "true" : "false";
            }
            else if (this.typegen.typecheckIsName(argtype, /^NSCore::ISOTime$/) || this.typegen.typecheckIsName(argtype, /^NSCore::Regex$/)) {
                return this.typegen.assembly.subtypeOf(argtype, moftype) ? "true" : "false";
            }
            else if (this.typegen.typecheckTuple(argtype)) {
                if(this.typegen.assembly.subtypeOf(this.typegen.tupleType, moftype)) {
                    return "true";
                }

                if(this.typegen.assembly.subtypeOf(moftype, this.typegen.apiType)) {
                    return `((BSQ_GET_VALUE_PTR(${arg}, BSQTuple)->flag & DATA_KIND_API_FLAG) != DATA_KIND_CLEAR_FLAG)`;
                }

                if(this.typegen.assembly.subtypeOf(moftype, this.typegen.podType)) {
                    return `((BSQ_GET_VALUE_PTR(${arg}, BSQTuple)->flag & DATA_KIND_POD_FLAG) != DATA_KIND_CLEAR_FLAG)`;
                }

                return "false";
            }
            else if (this.typegen.typecheckRecord(argtype)) {
                if(this.typegen.assembly.subtypeOf(this.typegen.tupleType, moftype)) {
                    return "true";
                }

                if(this.typegen.assembly.subtypeOf(moftype, this.typegen.apiType)) {
                    return `((BSQ_GET_VALUE_PTR(${arg}, BSQRecord)->flag & DATA_KIND_API_FLAG) != DATA_KIND_CLEAR_FLAG)`;
                }

                if(this.typegen.assembly.subtypeOf(moftype, this.typegen.podType)) {
                    return `((BSQ_GET_VALUE_PTR(${arg}, BSQRecord)->flag & DATA_KIND_POD_FLAG) != DATA_KIND_CLEAR_FLAG)`;
                }

                return "false";
            }
            else if(this.typegen.typecheckUEntity(argtype)) {
                return this.typegen.assembly.subtypeOf(argtype, moftype) ? "true" : "false";
            }
            else {
                const simplenominalok = moftype.options.every((copt) => {
                    const cc = this.typegen.getMIRType(copt.trkey);

                    const maybetuple = this.typegen.assembly.subtypeOf(this.typegen.tupleType, cc);
                    const mayberecord = this.typegen.assembly.subtypeOf(this.typegen.recordType, cc);
                    const maybepod = this.typegen.assembly.subtypeOf(this.typegen.podType, cc);
                    const maybeapi = this.typegen.assembly.subtypeOf(this.typegen.apiType, cc);

                    return !(maybetuple || mayberecord || maybepod || maybeapi);
                });

                if(simplenominalok) {
                    return this.generateConceptArrayLookup(`getNominalTypeOf_Value(${arg})`, oftype);
                }
                else {
                    return this.generateSubtypeConceptCheck(arg, argtype, oftype);
                }
            }
        }
    }

    generateTypeCheck(arg: string, argtype: MIRType, inferargtype: MIRType, oftype: MIRType): string {
        if(inferargtype.trkey !== argtype.trkey) {
            arg = this.typegen.coerce(arg, argtype, inferargtype);
        }

        if(this.typegen.assembly.subtypeOf(inferargtype, oftype)) {
            return "true";
        }

        const tests = oftype.options.map((topt) => {
            const mtype = this.typegen.getMIRType(topt.trkey);
            assert(mtype !== undefined, "We should generate all the component types by default??");

            if(topt instanceof MIREntityType) {
                return this.generateFastEntityTypeCheck(arg, inferargtype, topt);
            }
            else if (topt instanceof MIRConceptType) {
                return this.generateFastConceptTypeCheck(arg, inferargtype, topt);
            }
            else if (topt instanceof MIRTupleType) {
                return this.generateFastTupleTypeCheck(arg, inferargtype, topt);
            }
            else {
                assert(topt instanceof MIRRecordType);

                return this.generateFastRecordTypeCheck(arg, inferargtype, topt as MIRRecordType);
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
            return `(${tests.join(" || ")})`
        }
    }

    generateStmt(op: MIROp): string | undefined {
        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const lcv = op as MIRLoadConst;
                return `${this.varToCppName(lcv.trgt)} = ${this.generateConstantExp(lcv.src, this.getArgType(lcv.trgt))};`;
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
                return `${this.varToCppName(lav.trgt)} = ${this.argToCpp(lav.name, this.getArgType(lav.trgt))};`;
            }
            case MIROpTag.MIRAccessLocalVariable: {
                const llv = op as MIRAccessLocalVariable;
                return `${this.varToCppName(llv.trgt)} = ${this.argToCpp(llv.name, this.getArgType(llv.trgt))};`;
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
                return NOT_IMPLEMENTED<string>("MIRConstructorPrimaryCollectionCopies");
            }
            case MIROpTag.MIRConstructorPrimaryCollectionMixed: {
                return NOT_IMPLEMENTED<string>("MIRConstructorPrimaryCollectionMixed");
            }
            case MIROpTag.MIRConstructorTuple: {
                return this.generateMIRConstructorTuple(op as MIRConstructorTuple);
            }
            case MIROpTag.MIRConstructorRecord: {
               return this.generateMIRConstructorRecord(op as MIRConstructorRecord);
            }
            case MIROpTag.MIRConstructorEphemeralValueList:
                return this.generateMIRConstructorEphemeralValueList(op as MIRConstructorEphemeralValueList);
            case MIROpTag.MIRAccessFromIndex: {
                const ai = op as MIRAccessFromIndex;
                return `${this.varToCppName(ai.trgt)} = ${this.generateMIRAccessFromIndexExpression(ai.arg, ai.idx, this.typegen.getMIRType(ai.resultAccessType))};`;
            }
            case MIROpTag.MIRProjectFromIndecies: {
                const pi = op as MIRProjectFromIndecies;
                return this.generateMIRProjectFromIndecies(pi, this.typegen.getMIRType(pi.resultProjectType));
            }
            case MIROpTag.MIRAccessFromProperty: {
                const ap = op as MIRAccessFromProperty;
                return `${this.varToCppName(ap.trgt)} = ${this.generateMIRAccessFromPropertyExpression(ap.arg, ap.property, this.typegen.getMIRType(ap.resultAccessType))};`;
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
                return NOT_IMPLEMENTED<string>("MIRProjectFromTypeTuple");
            }
            case MIROpTag.MIRProjectFromTypeRecord: {
                return NOT_IMPLEMENTED<string>("MIRProjectFromTypeRecord");
            }
            case MIROpTag.MIRProjectFromTypeNominal: {
                return NOT_IMPLEMENTED<string>("MIRProjectFromTypeConcept");
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
                return this.generateMIRStructuredExtendObject(so);
            }
            case MIROpTag.MIRInvokeFixedFunction: {
                const invk = op as MIRInvokeFixedFunction;
                return this.generateMIRInvokeFixedFunction(invk);
            }
            case MIROpTag.MIRInvokeVirtualTarget: {
                return NOT_IMPLEMENTED<string>("MIRInvokeVirtualTarget");
            }
            case MIROpTag.MIRPrefixOp: {
                const pfx = op as MIRPrefixOp;
                if (pfx.op === "!") {
                    const tval = this.generateTruthyConvert(pfx.arg);
                    return `${this.varToCppName(pfx.trgt)} = !${tval};`;
                }
                else {
                    if (pfx.op === "-") {
                        return `${this.varToCppName(pfx.trgt)} = (${this.argToCpp(pfx.arg, this.typegen.intType)}).negate();`;
                    }
                    else {
                        return `${this.varToCppName(pfx.trgt)} = ${this.argToCpp(pfx.arg, this.typegen.intType)};`;
                    }
                }
            }
            case MIROpTag.MIRBinOp: {
                const bop = op as MIRBinOp;
                if (bop.op === "+" || bop.op === "-" || bop.op === "*") {
                    return `${this.varToCppName(bop.trgt)} = ${this.argToCpp(bop.lhs, this.typegen.intType)} ${bop.op} ${this.argToCpp(bop.rhs, this.typegen.intType)};`;
                }
                else if (bop.op === "/") {
                    return `if(${this.argToCpp(bop.lhs, this.typegen.intType)}.isZero()) { BSQ_ABORT("Div by 0", "${filenameClean(this.currentFile)}", ${op.sinfo.line}); } ${this.varToCppName(bop.trgt)} = ${this.argToCpp(bop.lhs, this.typegen.intType)} / ${this.argToCpp(bop.rhs, this.typegen.intType)};`;
                }
                else {
                    return `if(${this.argToCpp(bop.lhs, this.typegen.intType)}.isZero()) { BSQ_ABORT("Mod by 0", "${filenameClean(this.currentFile)}", ${op.sinfo.line}); } ${this.varToCppName(bop.trgt)} = ${this.argToCpp(bop.lhs, this.typegen.intType)} % ${this.argToCpp(bop.rhs, this.typegen.intType)};`;
                }
            }
            case MIROpTag.MIRGetKey: {
                return NOT_IMPLEMENTED<string>("MIRGetKey");
            }
            case MIROpTag.MIRBinEq: {
                const beq = op as MIRBinEq;

                const lhvtypeinfer = this.typegen.getMIRType(beq.lhsInferType);
                const rhvtypeinfer = this.typegen.getMIRType(beq.rhsInferType);
                return `${this.varToCppName(beq.trgt)} = ${this.generateEquals(beq.op, lhvtypeinfer, beq.lhs, rhvtypeinfer, beq.rhs)};`;
            }
            case MIROpTag.MIRBinCmp: {
                const bcmp = op as MIRBinCmp;

                const lhvtypeinfer = this.typegen.getMIRType(bcmp.lhsInferType);
                const rhvtypeinfer = this.typegen.getMIRType(bcmp.rhsInferType);
                return `${this.varToCppName(bcmp.trgt)} = ${this.generateCompare(bcmp.op, lhvtypeinfer, bcmp.lhs, rhvtypeinfer, bcmp.rhs)};`;
            }
            case MIROpTag.MIRIsTypeOfNone: {
                const ton = op as MIRIsTypeOfNone;
                return `${this.varToCppName(ton.trgt)} = ${this.generateNoneCheck(ton.arg)};`;
            }
            case MIROpTag.MIRIsTypeOfSome: {
                const tos = op as MIRIsTypeOfSome;
                return `${this.varToCppName(tos.trgt)} = !${this.generateNoneCheck(tos.arg)};`;
           }
            case MIROpTag.MIRIsTypeOf: {
                const top = op as MIRIsTypeOf;
                const oftype = this.typegen.getMIRType(top.oftype);
                const argtype = this.getArgType(top.arg);

                return `${this.varToCppName(top.trgt)} = ${this.generateTypeCheck(this.argToCpp(top.arg, argtype), argtype, oftype, true)};`;
            }
            case MIROpTag.MIRRegAssign: {
                const regop = op as MIRRegAssign;
                return `${this.varToCppName(regop.trgt)} = ${this.argToCpp(regop.src, this.getArgType(regop.trgt))};`;
            }
            case MIROpTag.MIRTruthyConvert: {
                const tcop = op as MIRTruthyConvert;
                return `${this.varToCppName(tcop.trgt)} = ${this.generateTruthyConvert(tcop.src)};`;
            }
            case MIROpTag.MIRLogicStore: {
                const llop = op as MIRLogicStore;
                return `${this.varToCppName(llop.trgt)} = (${this.argToCpp(llop.lhs, this.typegen.boolType)} ${llop.op} ${this.argToCpp(llop.rhs, this.typegen.boolType)});`;
            }
            case MIROpTag.MIRVarStore: {
                const vsop = op as MIRVarStore;
                return `${this.varToCppName(vsop.name)} = ${this.argToCpp(vsop.src, this.getArgType(vsop.name))};`;
            }
            case MIROpTag.MIRReturnAssign: {
                const raop = op as MIRReturnAssign;
                return `${this.varToCppName(raop.name)} = ${this.argToCpp(raop.src, this.getArgType(raop.name))};`;
            }
            case MIROpTag.MIRAbort: {
                const aop = (op as MIRAbort);
                return `BSQ_ABORT("${aop.info}", "${filenameClean(this.currentFile)}", ${aop.sinfo.line});`;
            }
            case MIROpTag.MIRDebug: {
                //debug is a nop in AOT release mode but we allow it for our debugging purposes
                const dbgop = op as MIRDebug;
                if (dbgop.value === undefined) {
                    return "assert(false);";
                }
                else {
                    return `{ std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv; std::cout << conv.to_bytes(Runtime::diagnostic_format(${this.argToCpp(dbgop.value, this.typegen.anyType)})) << "\\n"; }`;
                }
            }
            case MIROpTag.MIRJump: {
                const jop = op as MIRJump;
                return `goto ${this.labelToCpp(jop.trgtblock)};`;
            }
            case MIROpTag.MIRJumpCond: {
                const cjop = op as MIRJumpCond;
                return `if(${this.generateTruthyConvert(cjop.arg)}) {goto ${this.labelToCpp(cjop.trueblock)};} else {goto ${cjop.falseblock};}`;
            }
            case MIROpTag.MIRJumpNone: {
                const njop = op as MIRJumpNone;
                return `if(${this.generateNoneCheck(njop.arg)}) {goto ${this.labelToCpp(njop.noneblock)};} else {goto ${njop.someblock};}`;
            }
            case MIROpTag.MIRPhi: {
                return undefined; //handle this as a special case in the block processing code
            }
            case MIROpTag.MIRVarLifetimeStart:
            case MIROpTag.MIRVarLifetimeEnd: {
                return undefined;
            }
            default: {
                return NOT_IMPLEMENTED<string>(`Missing case ${op.tag}`);
            }
        }
    }

    generateBlock(block: MIRBasicBlock) {
        let gblock: string[] = [];

        let blocki = 0;
        while (blocki < block.ops.length - 1 && block.ops[blocki] instanceof MIRPhi) {
            const phiop = block.ops[blocki] as MIRPhi;
            phiop.src.forEach((src, fblock) => {
                const assign = `${this.varToCppName(phiop.trgt)} = ${this.argToCpp(src, this.getArgType(phiop.trgt))};`;
                const inblock = this.generatedBlocks.get(fblock) as string[];

                //last entry is the jump so put before that but after all other statements
                const jmp = inblock[inblock.length - 1];
                inblock[inblock.length - 1] = assign;
                inblock.push(jmp);
            });

            ++blocki;
        }

        while (blocki < block.ops.length) {
            const gop = this.generateStmt(block.ops[blocki]);
            if (gop !== undefined) {
                gblock.push(gop);
            }

            ++blocki;
        }

        if (block.label === "exit") {
            if (this.typegen.maybeRefableCountableType(this.currentRType)) {
                if(this.typegen.isTupleType(this.currentRType)) {
                    const procs: string[] = [];
                    const maxlen = CPPTypeEmitter.getTupleTypeMaxLength(this.currentRType);
                    for (let i = 0; i < maxlen; ++i) {
                        const cvn = this.varNameToCppName(`$callerslot$${i}`);
                        procs.push(`BSQRefScopeMgr::processCallRefAny(${cvn}, _return_${this.typegen.generateFixedTupleAccessor(i)});`);
                    }
                    gblock.push(procs.join(" "));
                }
                else if(this.typegen.isRecordType(this.currentRType)) {
                    const procs: string[] = [];
                    const allprops = CPPTypeEmitter.getRecordTypeMaxPropertySet(this.currentRType);
                    for (let i = 0; i < allprops.length; ++i) {
                        const cvn = this.varNameToCppName(`$callerslot$${allprops[i]}`);
                        if (this.typegen.isKnownLayoutRecordType(this.currentRType)) {
                            procs.push(`BSQRefScopeMgr::processCallRefAny(${cvn}, _return_${this.typegen.generateKnownRecordAccessor(this.currentRType, allprops[i])});`);
                        }
                        else {
                            procs.push(`BSQRefScopeMgr::processCallRefAny(${cvn}, _return_${this.typegen.generateFixedRecordAccessor(allprops[i])});`);
                        }
                    }
                    gblock.push(procs.join(" "));
                }
                else if (this.typegen.isUEntityType(this.currentRType)) {
                    const cslotvar = this.varNameToCppName("$callerslot$");
                    if (this.assembly.subtypeOf(this.typegen.noneType, this.currentRType)) {
                        gblock.push(`BSQRefScopeMgr::processCallRefNoneable(${cslotvar}, _return_);`);
                    }
                    else {
                        gblock.push(`BSQRefScopeMgr::processCallReturnFast(${cslotvar}, _return_);`);
                    }
                }
                else {
                    const cslotvar = this.varNameToCppName("$callerslot$");
                    gblock.push(`BSQRefScopeMgr::processCallRefAny(${cslotvar}, _return_);`);
                }
            }

            gblock.push("return _return_;");
        }

        this.generatedBlocks.set(block.label, gblock);
    }

    generateCPPVarDecls(body: MIRBody, params: MIRFunctionParameter[]): string {
        const scopevar = this.varNameToCppName("$scope$");
        const refscope = "    " + (this.typegen.scopectr !== 0 ? `BSQRefScope<${this.typegen.scopectr}> ${scopevar};` : ";");

        let vdecls = new Map<string, string[]>();
        (body.vtypes as Map<string, string>).forEach((tkey, name) => {
            if (params.findIndex((p) => p.name === name) === -1) {
                const declt = this.typegen.typeToCPPType(this.typegen.getMIRType(tkey), "decl");
                if (!vdecls.has(declt)) {
                    vdecls.set(declt, [] as string[]);
                }

                (vdecls.get(declt) as string[]).push(this.varNameToCppName(name));
            }
        });
        let vdeclscpp: string[] = [];
        if (vdecls.has("bool")) {
            vdeclscpp.push(`bool ${(vdecls.get("bool") as string[]).join(", ")};`);
        }
       [...vdecls].sort((a, b) => a[0].localeCompare(b[0])).forEach((kv) => {
            if (kv[0] !== "bool") {
                vdeclscpp.push(kv[1].map((vname) => `${kv[0]} ${vname}`).join("; ") + ";");
            }
        });

        return [refscope, ...vdeclscpp].join("\n    ");
    }

    generateCPPInvoke(idecl: MIRInvokeDecl): { fwddecl: string, fulldecl: string } {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.getMIRType(idecl.resultType);
        this.typegen.scopectr = 0;

        const args = idecl.params.map((arg) => `${this.typegen.typeToCPPType(this.typegen.getMIRType(arg.type), "parameter")} ${this.varNameToCppName(arg.name)}`);
        const restype = this.typegen.typeToCPPType(this.typegen.getMIRType(idecl.resultType), "return");

        if (this.typegen.maybeRefableCountableType(this.typegen.getMIRType(idecl.resultType))) {
            if (this.typegen.isTupleType(this.currentRType)) {
                const maxlen = CPPTypeEmitter.getTupleTypeMaxLength(this.currentRType);
                for (let i = 0; i < maxlen; ++i) {
                    const cslotvar = this.varNameToCppName(`$callerslot$${i}`);
                    args.push(`BSQRef** ${cslotvar}`);
                }
            }
            else if (this.typegen.isRecordType(this.currentRType)) {
                const allprops = CPPTypeEmitter.getRecordTypeMaxPropertySet(this.currentRType);
                for (let i = 0; i < allprops.length; ++i) {
                    const cslotvar = this.varNameToCppName(`$callerslot$${allprops[i]}`);
                    args.push(`BSQRef** ${cslotvar}`);
                }
            }
            else {
                const cslotvar = this.varNameToCppName("$callerslot$");
                args.push(`BSQRef** ${cslotvar}`);
            }
        }
        const decl = `${restype} ${this.invokenameToCPP(idecl.key)}(${args.join(", ")})`;

        if (idecl instanceof MIRInvokeBodyDecl) {
            this.vtypes = new Map<string, MIRType>();
            (idecl.body.vtypes as Map<string, string>).forEach((tkey, name) => {
                this.vtypes.set(name, this.assembly.typeMap.get(tkey) as MIRType);
            });

            this.generatedBlocks = new Map<string, string[]>();

            const blocks = topologicalOrder((idecl as MIRInvokeBodyDecl).body.body);
            for (let i = 0; i < blocks.length; ++i) {
                this.generateBlock(blocks[i]);
            }

            if (idecl.preconditions.length === 0 && idecl.postconditions.length === 0) {
                const blockstrs = [...this.generatedBlocks].map((blck) => {
                    const lbl = `${this.labelToCpp(blck[0])}:\n`;
                    const stmts = blck[1].map((stmt) => "    " + stmt).join("\n");

                    if(lbl.startsWith("entry:")) {
                        return stmts;
                    }
                    else {
                        return lbl + stmts;
                    }
                });

                const scopestrs = this.generateCPPVarDecls(idecl.body, idecl.params);

                return { fwddecl: decl + ";", fulldecl: `${decl}\n{\n${scopestrs}\n\n${blockstrs.join("\n\n")}\n}\n` };
            }
            else {
                let prestr = ";";
                const preargs = idecl.params.map((arg) => this.varNameToCppName(arg.name));

                //
                //TODO -- ref parms don't get expanded correctly here -- need to coordinate with def and call here
                //
                let poststr = "   return _return_;";
                const postargs = [...idecl.params.map((arg) => this.varNameToCppName(arg.name)), "_return_"];

                if (idecl.preconditions.length !== 0) {
                    const preinvoke = `${this.invokenameToCPP(MIRKeyGenerator.generateBodyKey("pre", idecl.key))}(${preargs.join(", ")})`;
                    prestr = `    ${preinvoke};`;
                }
                
                if(idecl.postconditions.length !== 0) {
                    const postinvoke = `${this.invokenameToCPP(MIRKeyGenerator.generateBodyKey("post", idecl.key))}(${postargs.join(", ")})`;
                    poststr = `    ${postinvoke};\n   return _return_;`;
                }

                const blockstrs = [...this.generatedBlocks].map((blck) => {
                    const lbl = `${this.labelToCpp(blck[0])}:\n`;
                    const stmts = blck[1].map((stmt) => "    " + stmt);
                    if(blck[0] === "exit") {
                        stmts[stmts.length - 1] = poststr;
                    }

                    if(lbl.startsWith("entry:")) {
                        return stmts.join("\n");
                    }
                    else {
                        return lbl + stmts.join("\n");
                    }
                });

                const scopestrs = this.generateCPPVarDecls(idecl.body, idecl.params);

                return { fwddecl: decl + ";", fulldecl: `${decl}\n{\n${prestr}\n${scopestrs}\n\n${blockstrs.join("\n\n")}\n}\n` };
            }
        }
        else {
            assert(idecl instanceof MIRInvokePrimitiveDecl);

            const params = idecl.params.map((arg) => this.varNameToCppName(arg.name));
            return { fwddecl: decl + ";", fulldecl: `${decl} { ${this.generateBuiltinBody(idecl as MIRInvokePrimitiveDecl, params)} }\n` };
        }
    }

    generateCPPPre(prekey: MIRBodyKey, idecl: MIRInvokeDecl): string {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.boolType;
        this.typegen.scopectr = 0;

        const args = idecl.params.map((arg) => `${this.typegen.typeToCPPType(this.typegen.getMIRType(arg.type), "parameter")} ${this.varNameToCppName(arg.name)}`);

        const decls = idecl.preconditions.map((pc, i) => {
            this.vtypes = new Map<string, MIRType>();
            (pc[0].vtypes as Map<string, string>).forEach((tkey, name) => {
                this.vtypes.set(name, this.typegen.getMIRType(tkey));
            });

            this.generatedBlocks = new Map<string, string[]>();

            const blocks = topologicalOrder(pc[0].body);
            for (let i = 0; i < blocks.length; ++i) {
                this.generateBlock(blocks[i]);
            }

            const blockstrs = [...this.generatedBlocks].map((blck) => {
                const lbl = `${this.labelToCpp(blck[0])}:\n`;
                const stmts = blck[1].map((stmt) => "    " + stmt).join("\n");

                if(lbl.startsWith("entry:")) {
                    return stmts;
                }
                else {
                    return lbl + stmts;
                }
            });

            const decl = `bool ${this.invokenameToCPP(prekey)}${i}(${args.join(", ")})`;
            const scopestrs = this.generateCPPVarDecls(pc[0], idecl.params);

            const call = `${this.invokenameToCPP(prekey)}${i}(${idecl.params.map((p) => this.varNameToCppName(p.name)).join(", ")})`;

            return [`${decl}\n{\n${scopestrs}\n\n${blockstrs.join("\n\n")}\n}\n`, call];
        });

        const declroot = `void ${this.invokenameToCPP(prekey)}(${args.join(", ")})`;
        const declbody = `if(!(${decls.map((cc) => cc[1]).join(" && ")})) { BSQ_ABORT("Pre-condition Failure: ${idecl.iname}", "${filenameClean(this.currentFile)}", ${idecl.sourceLocation.line}); }`
        return `${decls.map((cc) => cc[0]).join("\n")}\n\n${declroot}\n{\n    ${declbody}\n}`;
    }

    generateCPPPost(postkey: MIRBodyKey, idecl: MIRInvokeDecl): string {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.boolType;
        this.typegen.scopectr = 0;
        const restype = this.typegen.getMIRType(idecl.resultType);

        const args = idecl.params.map((arg) => `${this.typegen.typeToCPPType(this.typegen.getMIRType(arg.type), "parameter")} ${this.varNameToCppName(arg.name)}`);
        args.push(`${this.typegen.typeToCPPType(restype, "parameter")} __result__`);

        const decls = idecl.postconditions.map((pc, i) => {
            this.vtypes = new Map<string, MIRType>();
            (pc.vtypes as Map<string, string>).forEach((tkey, name) => {
                this.vtypes.set(name, this.typegen.getMIRType(tkey));
            });

            this.generatedBlocks = new Map<string, string[]>();

            const blocks = topologicalOrder(pc.body);
            for (let i = 0; i < blocks.length; ++i) {
                this.generateBlock(blocks[i]);
            }

            const blockstrs = [...this.generatedBlocks].map((blck) => {
                const lbl = `${this.labelToCpp(blck[0])}:\n`;
                const stmts = blck[1].map((stmt) => "    " + stmt).join("\n");

                if (lbl.startsWith("entry:")) {
                    return stmts;
                }
                else {
                    return lbl + stmts;
                }
            });

            const decl = `bool ${this.invokenameToCPP(postkey)}${i}(${args.join(", ")})`;
            const scopestrs = this.generateCPPVarDecls(pc, [...idecl.params, new MIRFunctionParameter("__result__", idecl.resultType)]);

            const call = `${this.invokenameToCPP(postkey)}${i}(${[...idecl.params.map((p) => this.varNameToCppName(p.name)), "__result__"].join(", ")})`;

            return [`${decl}\n{\n${scopestrs}\n\n${blockstrs.join("\n\n")}\n}\n`, call];
        });

        const declroot = `void ${this.invokenameToCPP(postkey)}(${args.join(", ")})`;
        const declbody = `if(!(${decls.map((cc) => cc[1]).join(" && ")})) { BSQ_ABORT("Post-condition Failure: ${idecl.iname}", "${filenameClean(this.currentFile)}", ${idecl.sourceLocation.line}); }`
        return `${decls.map((cc) => cc[0]).join("\n")}\n\n${declroot}\n{\n    ${declbody}\n}`;
    }

    generateCPPInv(invkey: MIRBodyKey, idecl: MIREntityTypeDecl): string {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.boolType;
        this.typegen.scopectr = 0;

        const decls = idecl.invariants.map((ic, i) => {
            this.vtypes = new Map<string, MIRType>();
            (ic.vtypes as Map<string, string>).forEach((tkey, name) => {
                this.vtypes.set(name, this.typegen.getMIRType(tkey));
            });

            this.generatedBlocks = new Map<string, string[]>();

            const blocks = topologicalOrder(ic.body);
            for (let i = 0; i < blocks.length; ++i) {
                this.generateBlock(blocks[i]);
            }

            const blockstrs = [...this.generatedBlocks].map((blck) => {
                const lbl = `${this.labelToCpp(blck[0])}:\n`;
                const stmts = blck[1].map((stmt) => "    " + stmt).join("\n");

                if(lbl.startsWith("entry:")) {
                    return stmts;
                }
                else {
                    return lbl + stmts;
                }
            });

            const decl = `bool ${this.invokenameToCPP(invkey)}${i}(${this.typegen.typeToCPPType(this.typegen.getMIRType(idecl.tkey), "parameter")} ${this.varNameToCppName("this")})`;
            const scopestrs = this.generateCPPVarDecls(idecl.invariants[0], [new MIRFunctionParameter("this", idecl.tkey)]);

            return [`${decl}\n{\n${scopestrs}\n\n${blockstrs.join("\n\n")}\n}\n`, `${this.invokenameToCPP(invkey)}${i}(${this.varNameToCppName("this")})`];
        });

        const declroot = `void ${this.invokenameToCPP(invkey)}(${this.typegen.typeToCPPType(this.typegen.getMIRType(idecl.tkey), "parameter")} ${this.varNameToCppName("this")})`;
        const declbody = `if(!(${decls.map((cc) => cc[1]).join(" && ")})) { BSQ_ABORT("Invariant Failure: ${idecl.ns}::${idecl.name}", "${filenameClean(this.currentFile)}", ${idecl.sourceLocation.line}); }`
        return `${decls.map((cc) => cc[0]).join("\n")}\n\n${declroot}\n{\n    ${declbody}\n}`;
    }

    generateCPPConst(constkey: MIRBodyKey, cdecl: MIRConstantDecl): { fwddecl: string, fulldecl: string } | undefined {
        this.currentFile = cdecl.srcFile;
        this.currentRType = this.typegen.getMIRType(cdecl.declaredType);
        this.typegen.scopectr = 0;

        if (CPPBodyEmitter.expBodyTrivialCheck(cdecl.value)) {
            return undefined;
        }

        const decltype = this.typegen.typeToCPPType(this.typegen.getMIRType(cdecl.declaredType), "decl");
        const flagname = `_flag_${this.invokenameToCPP(constkey)}`;
        const memoname = `_memo_${this.invokenameToCPP(constkey)}`;
        const gdecl = `bool ${flagname} = false; ${decltype} ${memoname};`;
        const qcheck = `    if (${flagname}) { return ${memoname}; }`;

        let rcvars = "";
        if(this.typegen.maybeRefableCountableType(this.typegen.getMIRType(cdecl.declaredType))) {
            if (this.typegen.isTupleType(this.currentRType)) {
                const procs: string[] = [];
                const maxlen = CPPTypeEmitter.getTupleTypeMaxLength(this.currentRType);
                for (let i = 0; i < maxlen; ++i) {
                    const cslotvar = this.varNameToCppName(`$callerslot$${i}`);
                    procs.push(`BSQRef** ${cslotvar};`);
                }
                rcvars = `    BSQRef* __CS_DUMMY__[${maxlen}] = {nullptr}; ${procs.join(" ")}`;
            }
            else if (this.typegen.isRecordType(this.currentRType)) {
                const procs: string[] = [];
                const allprops = CPPTypeEmitter.getRecordTypeMaxPropertySet(this.currentRType);
                for (let i = 0; i < allprops.length; ++i) {
                    const cslotvar = this.varNameToCppName(`$callerslot$${allprops[i]}`);
                    procs.push(`BSQRef** ${cslotvar} = __CS_DUMMY__ + ${i};`);
                }
                rcvars = `    BSQRef* __CS_DUMMY__[${allprops.length}] = {nullptr}; ${procs.join(" ")}`;
            }
            else {
                const cslotvar = this.varNameToCppName("$callerslot$");
                rcvars = `    BSQRef* __CS_DUMMY__ = nullptr; BSQRef** ${cslotvar} = &__CS_DUMMY__;`;
            }
        }

        const rupdate = `${memoname} = _return_;  ${flagname} = true;`;
        const restype = this.typegen.typeToCPPType(this.typegen.getMIRType(cdecl.declaredType), "return");
        const decl = `${restype} ${this.invokenameToCPP(constkey)}()`;

        this.vtypes = new Map<string, MIRType>();
        (cdecl.value.vtypes as Map<string, string>).forEach((tkey, name) => {
            this.vtypes.set(name, this.assembly.typeMap.get(tkey) as MIRType);
        });

        this.generatedBlocks = new Map<string, string[]>();

        const blocks = topologicalOrder(cdecl.value.body);
        for (let i = 0; i < blocks.length; ++i) {
            this.generateBlock(blocks[i]);
        }

        const blockstrs = [...this.generatedBlocks].map((blck) => {
            const lbl = `${this.labelToCpp(blck[0])}:\n`;
            const stmts = blck[1].map((stmt) => "    " + stmt).join("\n");

            if(lbl.startsWith("entry:")) {
                return stmts;
            }
            else {
                return lbl + stmts;
            }
        });

        const scopestrs = this.generateCPPVarDecls(cdecl.value, []);
        const jblockstrs = blockstrs.join("\n\n");

        const rstart = jblockstrs.indexOf("return _return_");
        const nblockstrs = jblockstrs.slice(0, rstart) + rupdate + "\n    " + jblockstrs.slice(rstart);

        return { fwddecl: decl + ";", fulldecl: `${gdecl}\n${decl}\n{\n${scopestrs}\n\n${qcheck}\n${rcvars}\n\n${nblockstrs}\n}\n` };
    }

    generateCPPFDefault(fdkey: MIRBodyKey, fdecl: MIRFieldDecl): { fwddecl: string, fulldecl: string } | undefined {
        this.currentFile = fdecl.srcFile;
        this.currentRType = this.typegen.getMIRType(fdecl.declaredType);
        this.typegen.scopectr = 0;

        if (CPPBodyEmitter.expBodyTrivialCheck(fdecl.value as MIRBody)) {
            return undefined;
        }

        const fdbody = fdecl.value as MIRBody;

        const decltype = this.typegen.typeToCPPType(this.typegen.getMIRType(fdecl.declaredType), "decl");
        const flagname = `_flag_${this.invokenameToCPP(fdkey)}`;
        const memoname = `_memo_${this.invokenameToCPP(fdkey)}`;
        const gdecl = `bool ${flagname} = false; ${decltype} ${memoname};`;
        const qcheck = `    if (${flagname}) { return ${memoname}; }`;

        let rcvars = "";
        if(this.typegen.maybeRefableCountableType(this.typegen.getMIRType(fdecl.declaredType))) {
            if (this.typegen.isTupleType(this.currentRType)) {
                const procs: string[] = [];
                const maxlen = CPPTypeEmitter.getTupleTypeMaxLength(this.currentRType);
                for (let i = 0; i < maxlen; ++i) {
                    const cslotvar = this.varNameToCppName(`$callerslot$${i}`);
                    procs.push(`BSQRef** ${cslotvar};`);
                }
                rcvars = `    BSQRef* __CS_DUMMY__[${maxlen}] = {nullptr}; ${procs.join(" ")}`;
            }
            else if (this.typegen.isRecordType(this.currentRType)) {
                const procs: string[] = [];
                const allprops = CPPTypeEmitter.getRecordTypeMaxPropertySet(this.currentRType);
                for (let i = 0; i < allprops.length; ++i) {
                    const cslotvar = this.varNameToCppName(`$callerslot$${allprops[i]}`);
                    procs.push(`BSQRef** ${cslotvar} = __CS_DUMMY__ + ${i};`);
                }
                rcvars = `    BSQRef* __CS_DUMMY__[${allprops.length}] = {nullptr}; ${procs.join(" ")}`;
            }
            else {
                const cslotvar = this.varNameToCppName("$callerslot$");
                rcvars = `    BSQRef* __CS_DUMMY__ = nullptr; BSQRef** ${cslotvar} = &__CS_DUMMY__;`;
            }
        }

        const rupdate = `${memoname} = _return_;  ${flagname} = true;`;

        const restype = this.typegen.typeToCPPType(this.typegen.getMIRType(fdecl.declaredType), "return");
        const decl = `${restype} ${this.invokenameToCPP(fdkey)}()`;

        this.vtypes = new Map<string, MIRType>();
        (fdbody.vtypes as Map<string, string>).forEach((tkey, name) => {
            this.vtypes.set(name, this.assembly.typeMap.get(tkey) as MIRType);
        });

        this.generatedBlocks = new Map<string, string[]>();

        const blocks = topologicalOrder(fdbody.body);
        for (let i = 0; i < blocks.length; ++i) {
            this.generateBlock(blocks[i]);
        }

        const blockstrs = [...this.generatedBlocks].map((blck) => {
            const lbl = `${this.labelToCpp(blck[0])}:\n`;
            const stmts = blck[1].map((stmt) => "    " + stmt).join("\n");

            if(lbl.startsWith("entry:")) {
                return stmts;
            }
            else {
                return lbl + stmts;
            }
        });

        const scopestrs = this.generateCPPVarDecls(fdbody, []);
        const jblockstrs = blockstrs.join("\n\n");

        const rstart = jblockstrs.indexOf("return _return_;");
        const nblockstrs = jblockstrs.slice(0, rstart) + rupdate + "\n    " + jblockstrs.slice(rstart);

        return { fwddecl: decl + ";", fulldecl: `${gdecl}\n${decl}\n{\n${scopestrs}\n\n${qcheck}\n${rcvars}\n\n${nblockstrs}\n}\n` };
    }

    generateBuiltinBody(idecl: MIRInvokePrimitiveDecl, params: string[]): string {
        const rtype = this.typegen.getMIRType(idecl.resultType);
        const scopevar = this.varNameToCppName("$scope$");

        let bodystr = ";";
        switch (idecl.implkey) {
            case "list_size": {
                bodystr = `auto _return_ = ${params[0]}->entries.size();`
                break;
            }
            case "list_unsafe_at": {
                bodystr = "auto _return_ = " + this.typegen.coerce(`${params[0]}->entries[${params[1]}.getInt64()]`, this.typegen.anyType, rtype) + ";";
                break;
            }
            case "list_unsafe_add": {
                bodystr = `auto _return_ = ${params[0]}->unsafeAdd(${this.typegen.coerce(params[1], this.typegen.getMIRType(idecl.params[1].type), this.typegen.anyType)});`
                break;
            }
            case "list_unsafe_set": {
                bodystr = `auto _return_ = ${params[0]}->unsafeSet(${params[1]}, ${this.typegen.coerce(params[2], this.typegen.getMIRType(idecl.params[2].type), this.typegen.anyType)});`
                break;
            }
            case "list_destructive_add": {
                bodystr = `auto _return_ = ${params[0]}->destructiveAdd(${this.typegen.coerce(params[1], this.typegen.getMIRType(idecl.params[1].type), this.typegen.anyType)});`
                break;
            }
            case "keylist_cons": {
                const tag = `MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(rtype.trkey)}`;
                const klparam = this.typegen.generateConstructorArgInc(this.typegen.getMIRType(idecl.params[0].type), params[0]);
                const vparam = this.typegen.generateConstructorArgInc(this.typegen.getMIRType(idecl.params[1].type), params[1]);
                bodystr = `auto _return_ = ${scopevar}.addAllocRef<${this.typegen.scopectr++}, BSQKeyList>(new BSQKeyList(${tag}, ${klparam}, ${vparam}));`
                break;
            }
            case "keylist_getkey": {
                bodystr = `auto _return_ = ${params[0]}->key;`
                break;
            }
            case "keylist_gettail": {
                bodystr = `auto _return_ = ${params[0]}->tail;`
                break;
            }
            case "set_size":
            case "map_size": {
                bodystr = `auto _return_ = ${params[0]}->entries.size();`
                break;
            }
            case "set_has_key":
            case "map_has_key": {
                bodystr = "auto _return_ = " + `${params[0]}->entries.find(${params[1]}) != ${params[0]}->entries.cend()` + ";";
                break;
            }
            case "set_at_val":
            case "map_at_val": {
                bodystr = "auto _return_ = " + this.typegen.coerce(`(${params[0]}->entries.find(${params[1]}))->second`, this.typegen.anyType, rtype) + ";";
                break;
            }
            case "set_get_keylist":
            case "map_get_keylist": {
                bodystr = "auto _return_ = " + `${params[0]}->keys` + ";";
                break;
            }
            case "set_clear_val": 
            case "map_clear_val": {
                bodystr = "auto _return_ = " + `${params[0]}->clearKey(${params[1]}, ${params[2]})` + ";";
                break;
            }
            case "set_unsafe_update":  
            case "map_unsafe_update": {
                bodystr = "auto _return_ = " + `${params[0]}->update(${params[1]}, ${this.typegen.coerce(params[2], this.typegen.getMIRType(idecl.params[2].type), this.typegen.anyType)})` + ";";
                break;
            }
            case "set_destuctive_update":
            case "map_destuctive_update": {
                bodystr = "auto _return_ = " + `${params[0]}->destructiveUpdate(${params[1]}, ${this.typegen.coerce(params[2], this.typegen.getMIRType(idecl.params[2].type), this.typegen.anyType)})` + ";";
                break;
            }
            case "set_unsafe_add":  
            case "map_unsafe_add": {
                bodystr = "auto _return_ = " + `${params[0]}->add(${params[1]}, ${this.typegen.coerce(params[2], this.typegen.getMIRType(idecl.params[2].type), this.typegen.anyType)}, ${params[3]})` + ";";
                break;
            }
            case "set_destuctive_add":
            case "map_destuctive_add": {
                bodystr = "auto _return_ = " + `${params[0]}->destructiveAdd(${params[1]}, ${this.typegen.coerce(params[2], this.typegen.getMIRType(idecl.params[2].type), this.typegen.anyType)}, ${params[3]})` + ";";
                break;
            }
            default: {
                bodystr = `[Builtin not defined -- ${idecl.iname}]`;
                break;
            }
        }

        const refscope = (this.typegen.scopectr !== 0 ? `BSQRefScope<${this.typegen.scopectr}> ${scopevar};` : ";");
        let returnmgr = "";
        if (this.typegen.maybeRefableCountableType(this.currentRType)) {
            if (this.typegen.isTupleType(this.currentRType)) {
                const procs: string[] = [];
                const maxlen = CPPTypeEmitter.getTupleTypeMaxLength(this.currentRType);
                for (let i = 0; i < maxlen; ++i) {
                    const cvn = this.varNameToCppName(`$callerslot$${i}`);
                    procs.push(`BSQRefScopeMgr::processCallRefAny(${cvn}, _return_${this.typegen.generateFixedTupleAccessor(i)});`);
                }
                returnmgr = procs.join(" ");
            }
            else if (this.typegen.isRecordType(this.currentRType)) {
                const procs: string[] = [];
                const allprops = CPPTypeEmitter.getRecordTypeMaxPropertySet(this.currentRType);
                for (let i = 0; i < allprops.length; ++i) {
                    const cvn = this.varNameToCppName(`$callerslot$${allprops[i]}`);
                    if (this.typegen.isKnownLayoutRecordType(this.currentRType)) {
                        procs.push(`BSQRefScopeMgr::processCallRefAny(${cvn}, _return_${this.typegen.generateKnownRecordAccessor(this.currentRType, allprops[i])});`);
                    }
                    else {
                        procs.push(`BSQRefScopeMgr::processCallRefAny(${cvn}, _return_${this.typegen.generateFixedRecordAccessor(allprops[i])});`);
                    }
                }
                returnmgr = procs.join(" ");
            }
            else if (this.typegen.isUEntityType(this.currentRType)) {
                const cslotvar = this.varNameToCppName("$callerslot$");
                if (this.assembly.subtypeOf(this.typegen.noneType, this.currentRType)) {
                    returnmgr = `BSQRefScopeMgr::processCallRefNoneable(${cslotvar}, _return_);`;
                }
                else {
                    returnmgr = `BSQRefScopeMgr::processCallReturnFast(${cslotvar}, _return_);`;
                }
            }
            else {
                const cslotvar = this.varNameToCppName("$callerslot$");
                returnmgr = `BSQRefScopeMgr::processCallRefAny(${cslotvar}, _return_);`;
            }
        }

        return "\n    " + refscope + "\n    " + bodystr + "\n    " + returnmgr + "\n    " + "return _return_;\n";
    }
}

export {
    CPPBodyEmitter
};
