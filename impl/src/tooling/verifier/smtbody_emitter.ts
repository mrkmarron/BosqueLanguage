//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIREntityType, MIREphemeralListType, MIRFieldDecl, MIRInvokeDecl, MIRRecordType, MIRRecordTypeEntry, MIRTupleType, MIRType } from "../../compiler/mir_assembly";
import { SMTTypeEmitter } from "./smttype_emitter";
import { MIRAbort, MIRAllTrue, MIRArgGuard, MIRArgument, MIRAssertCheck, MIRBinKeyEq, MIRCheckNoError, MIRConstantArgument, MIRConstantBigInt, MIRConstantBigNat, MIRConstantComplex, MIRConstantDecimal, MIRConstantFalse, MIRConstantFloat, MIRConstantInt, MIRConstantNat, MIRConstantNone, MIRConstantRational, MIRConstantRegex, MIRConstantString, MIRConstantTrue, MIRConstructorEphemeralList, MIRConstructorRecord, MIRConstructorRecordFromEphemeralList, MIRConstructorTuple, MIRConstructorTupleFromEphemeralList, MIRConvertValue, MIRDeadFlow, MIRDebug, MIRDeclareGuardFlagLocation, MIREntityProjectToEphemeral, MIREntityUpdate, MIREphemeralListExtend, MIRExtractResultOkValue, MIRFieldKey, MIRGlobalVariable, MIRGuard, MIRInvokeFixedFunction, MIRInvokeVirtualFunction, MIRInvokeVirtualOperator, MIRLoadConst, MIRLoadConstDataString, MIRLoadField, MIRLoadFromEpehmeralList, MIRLoadRecordProperty, MIRLoadRecordPropertySetGuard, MIRLoadTupleIndex, MIRLoadTupleIndexSetGuard, MIRLoadUnintVariableValue, MIRMaskGuard, MIRMultiLoadFromEpehmeralList, MIROp, MIRPrefixNotOp, MIRRecordHasProperty, MIRRecordProjectToEphemeral, MIRRecordUpdate, MIRRegisterArgument, MIRSetConstantGuardFlag, MIRSliceEpehmeralList, MIRStructuredAppendTuple, MIRStructuredJoinRecord, MIRTupleHasIndex, MIRTupleProjectToEphemeral, MIRTupleUpdate } from "../../compiler/mir_ops";
import { SMTCall, SMTCallWOptMask, SMTCond, SMTConst, SMTExp, SMTIf, SMTLet, SMTLetMulti, SMTMaskConstruct, SMTType, SMTVar, VerifierLevel } from "./smt_exp";
import { SourceInfo } from "../../ast/parser";
import { SMTAssembly, SMTErrorCode, SMTFunction } from "./smtassembly";

import * as assert from "assert";
import { on } from "process";

function NOT_IMPLEMENTED<T>(msg: string): T {
    throw new Error(`Not Implemented: ${msg}`);
}

class SMTBodyEmitter {
    readonly assembly: MIRAssembly;
    readonly smtasm: SMTAssembly;
    readonly typegen: SMTTypeEmitter;
    readonly level: VerifierLevel;

    private tmpvarctr = 0;

    private currentFile: string = "[No File]";
    private currentRType: MIRType;
    private currentSCC = new Set<string>();

    private subtypeOrderCtr = 0;
    subtypeFMap: Map<string, {order: number, decl: string}> = new Map<string, {order: number, decl: string}>();

    private pendingMask: SMTMaskConstruct[] = [];

    private requiredTypecheck: { inv: string, flowtype: MIRType, oftype: MIRType }[] = [];

    //!!!
    //See the methods generateLoadTupleIndexVirtual, generateLoadTupleIndexVirtual, etc for processing the entrues in these arrays
    //!!!

    private requiredLoadVirtualTupleIndex: { inv: string, argflowtype: MIRType, idx: number, resulttype: MIRType, guard: MIRGuard | undefined }[] = [];
    private requiredLoadVirtualRecordProperty: { inv: string, argflowtype: MIRType, pname: string, resulttype: MIRType, guard: MIRGuard | undefined }[] = [];
    private requiredLoadVirtualEntityField: { inv: string, argflowtype: MIRType, field: MIRFieldDecl, resulttype: MIRType }[] = [];
    
    private requiredProjectVirtualTupleIndex: { inv: string, argflowtype: MIRType, indecies: number[], resulttype: MIRType }[] = [];
    private requiredProjectVirtualRecordProperty: { inv: string, argflowtype: MIRType, properties: string[], resulttype: MIRType }[] = [];
    private requiredProjectVirtualEntityField: { inv: string, argflowtype: MIRType, fields: MIRFieldDecl[], resulttype: MIRType }[] = [];

    private generateTypeCheckName(argflowtype: MIRType, oftype: MIRType): string {
        return `$SubtypeCheck_${this.typegen.mangle(argflowtype.trkey)}_oftype_${this.typegen.mangle(oftype.trkey)}`;
    }

    private registerRequiredTypeCheck(argflowtype: MIRType, oftype: MIRType): string {
        const inv = this.generateTypeCheckName(argflowtype, oftype);
        if (this.requiredTypecheck.findIndex((rtc) => rtc.inv === inv) === -1) {
            this.requiredTypecheck.push({ inv: inv, flowtype: argflowtype, oftype: oftype });
        }

        return inv;
    }

    private generateUFConstantForType(tt: MIRType): string {
        const ctype = this.typegen.getSMTTypeFor(tt);
        const ufcname = `${ctype}@uicons_UF`;
        if(!this.smtasm.uninterpTypeConstructors.has(ufcname)) {
            this.smtasm.uninterpTypeConstructors.set(ufcname, ctype);
        }

        return ufcname;
    }

    private generateBoolForGuard(guard: MIRGuard): SMTExp {
        if(guard instanceof MIRMaskGuard) {
            return new SMTCall(`$MaskLoad_${guard.gsize}_@${guard.gindex}`, [new SMTVar(this.typegen.mangle(guard.gmask))]);
        }
        else {
            return this.argToSMT((guard as MIRArgGuard).greg);
        }
    }

    private generateAltForGuardStmt(arg: MIRArgument | undefined, oftype: MIRType): SMTExp {
        return arg !== undefined ? this.argToSMT(arg) : new SMTConst(this.generateUFConstantForType(oftype));
    }

    private generateLoadVirtualTupleInvName(argflowtype: MIRType, idx: number, resulttype: MIRType, guard: MIRGuard | undefined): string {
        return `$TupleLoad_${this.typegen.mangle(argflowtype.trkey)}_${idx}_${this.typegen.mangle(resulttype.trkey)}${guard !== undefined ? "_WG" : ""}`;
    }

    private generateLoadVirtualPropertyInvName(argflowtype: MIRType, pname: string, resulttype: MIRType, guard: MIRGuard | undefined): string {
        return `$RecordLoad_${this.typegen.mangle(argflowtype.trkey)}_${pname}_${this.typegen.mangle(resulttype.trkey)}${guard !== undefined ? "_WG" : ""}`;
    }

    private generateLoadVirtualFieldInvName(argflowtype: MIRType, fkey: MIRFieldKey, resulttype: MIRType): string {
        return `$EntityLoad_${this.typegen.mangle(argflowtype.trkey)}_${this.typegen.mangle(fkey)}_${this.typegen.mangle(resulttype.trkey)}`;
    }

    private generateProjectVirtualTupleInvName(argflowtype: MIRType, indecies: number[], resulttype: MIRType): string {
        const idxs = this.typegen.mangle(indecies.map((idx) => `${idx}`).join(","));
        return `$TupleProject_${this.typegen.mangle(argflowtype.trkey)}_${idxs}_${this.typegen.mangle(resulttype.trkey)}`;
    }

    private generateProjectVirtualRecordInvName(argflowtype: MIRType, properties: string[], resulttype: MIRType): string {
        const pnames = this.typegen.mangle(properties.join(","));
        return `$RecordProject_${this.typegen.mangle(argflowtype.trkey)}_${pnames}_${this.typegen.mangle(resulttype.trkey)}`;
    }

    private generateProjectVirtualEntityInvName(argflowtype: MIRType, fields: MIRFieldKey[], resulttype: MIRType): string {
        const fkeys = this.typegen.mangle(fields.join(","));
        return `$EntityProject_${this.typegen.mangle(argflowtype.trkey)}_${fkeys}_${this.typegen.mangle(resulttype.trkey)}`;
    }

    private generateLoadTupleIndexVirtual(geninfo: { inv: string, argflowtype: MIRType, idx: number, resulttype: MIRType, guard: MIRGuard | undefined }): SMTFunction {
        const ttuples = [...this.assembly.tupleDecls]
            .filter((tt) => {
                const mtt = MIRType.createSingle(tt[1]);
                return this.typegen.isUniqueTupleType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultType(geninfo.resulttype) : this.typegen.getSMTTypeFor(geninfo.resulttype);
        const ufcname = this.generateUFConstantForType(geninfo.resulttype);
        if(ttuples.length === 0) {
            const rbody = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, new SMTConst(ufcname), false) : new SMTConst(ufcname);
            return new SMTFunction(geninfo.inv, [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], undefined, rtype, rbody);
        }
        else {
            const ops = ttuples.map((tt) => {
                const mtt = MIRType.createSingle(tt);
                const test = new SMTCall(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

                const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
                const idxr = new SMTCall(this.typegen.generateTupleIndexGetFunction(tt, geninfo.idx), [argpp]);
                const crt = this.typegen.coerce(idxr, (geninfo.argflowtype.options[0] as MIRTupleType).entries[geninfo.idx].type, geninfo.resulttype);
                const action = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, crt, true) : crt;

                return {test: test, result: action};
            });

            const orelse = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, new SMTConst(ufcname), false) : new SMTConst(ufcname);

            return new SMTFunction(geninfo.inv, [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], undefined, rtype, new SMTCond(new SMTVar("arg"), ops, orelse));
        }
    }

    private generateLoadRecordPropertyVirtual(geninfo: { inv: string, argflowtype: MIRType, pname: string, resulttype: MIRType, guard: MIRGuard | undefined }): SMTFunction {
        const trecords = [...this.assembly.recordDecls]
            .filter((tt) => {
                const mtt = MIRType.createSingle(tt[1]);
                return this.typegen.isUniqueRecordType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultType(geninfo.resulttype) : this.typegen.getSMTTypeFor(geninfo.resulttype);
        const ufcname = this.generateUFConstantForType(geninfo.resulttype);
        if(trecords.length === 0) {
            const rbody = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, new SMTConst(ufcname), false) : new SMTConst(ufcname);
            return new SMTFunction(geninfo.inv, [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], undefined, rtype, rbody);
        }
        else {
            const ops = trecords.map((tt) => {
                const mtt = MIRType.createSingle(tt);
                const test = new SMTCall(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

                const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
                const idxr = new SMTCall(this.typegen.generateRecordPropertyGetFunction(tt, geninfo.pname), [argpp]);
                const crt = this.typegen.coerce(idxr, ((geninfo.argflowtype.options[0] as MIRRecordType).entries.find((vv) => vv.name === geninfo.pname) as MIRRecordTypeEntry).type, geninfo.resulttype);
                const action = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, crt, true) : crt;

                return {test: test, result: action};
            });

            const orelse = geninfo.guard !== undefined ? this.typegen.generateAccessWithSetGuardResultTypeConstructorLoad(geninfo.resulttype, new SMTConst(ufcname), false) : new SMTConst(ufcname);

            return new SMTFunction(geninfo.inv, [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], undefined, rtype, new SMTCond(new SMTVar("arg"), ops, orelse));
        }
    }

    private generateLoadEntityFieldVirtual(geninfo: { inv: string, argflowtype: MIRType, field: MIRFieldDecl, resulttype: MIRType }): SMTFunction {
        const tentities = [...this.assembly.recordDecls]
            .filter((tt) => {
                const mtt = MIRType.createSingle(tt[1]);
                return this.typegen.isUniqueEntityType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getSMTTypeFor(geninfo.resulttype);
        let ops = tentities.map((tt) => {
            const mtt = MIRType.createSingle(tt);
            const test = new SMTCall(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

            const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
            const action = new SMTCall(this.typegen.generateEntityFieldGetFunction(tt, geninfo.field.fkey), [argpp]);

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);

        return new SMTFunction(geninfo.inv, [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], undefined, rtype, new SMTCond(new SMTVar("arg"), ops, orelse));
    }

    private generateProjectTupleIndexVirtual(geninfo: { inv: string, argflowtype: MIRType, indecies: number[], resulttype: MIRType }): SMTFunction {
        const ttuples = [...this.assembly.tupleDecls]
            .filter((tt) => {
                const mtt = MIRType.createSingle(tt[1]);
                return this.typegen.isUniqueTupleType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getSMTTypeFor(geninfo.resulttype);
        let ops = ttuples.map((tt) => {
            const mtt = MIRType.createSingle(tt);
            const test = new SMTCall(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

            const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
            const pargs = geninfo.indecies.map((idx, i) => {
                const idxr = new SMTCall(this.typegen.generateTupleIndexGetFunction(geninfo.argflowtype.options[0] as MIRTupleType, idx), [argpp]);
                return this.typegen.coerce(idxr, (geninfo.argflowtype.options[0] as MIRTupleType).entries[idx].type, (geninfo.resulttype.options[0] as MIREphemeralListType).entries[i]);
            });
            const action = new SMTCall(this.typegen.getSMTConstructorName(geninfo.resulttype).cons, pargs);

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);
            
        return new SMTFunction(geninfo.inv, [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], undefined, rtype, new SMTCond(new SMTVar("arg"), ops, orelse));
    }

    private generateProjectRecordPropertyVirtual(geninfo: { inv: string, argflowtype: MIRType, properties: string[], resulttype: MIRType }): SMTFunction {
        const trecords = [...this.assembly.recordDecls]
            .filter((tt) => {
                const mtt = MIRType.createSingle(tt[1]);
                return this.typegen.isUniqueRecordType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getSMTTypeFor(geninfo.resulttype);
        let ops = trecords.map((tt) => {
            const mtt = MIRType.createSingle(tt);
            const test = new SMTCall(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

            const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
            const pargs = geninfo.properties.map((pname, i) => {
                const idxr = new SMTCall(this.typegen.generateRecordPropertyGetFunction(geninfo.argflowtype.options[0] as MIRRecordType, pname), [argpp]);
                return this.typegen.coerce(idxr, ((geninfo.argflowtype.options[0] as MIRRecordType).entries.find((vv) => vv.name === pname) as MIRRecordTypeEntry).type, (geninfo.resulttype.options[0] as MIREphemeralListType).entries[i]);
            });
            const action = new SMTCall(this.typegen.getSMTConstructorName(geninfo.resulttype).cons, pargs);

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);

        return new SMTFunction(geninfo.inv, [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], undefined, rtype, new SMTCond(new SMTVar("arg"), ops, orelse));
    }

    private generateProjectEntityFieldVirtual(geninfo: { inv: string, argflowtype: MIRType, fields: MIRFieldDecl[], resulttype: MIRType }): SMTFunction {
        const tentities = [...this.assembly.recordDecls]
            .filter((tt) => {
                const mtt = MIRType.createSingle(tt[1]);
                return this.typegen.isUniqueEntityType(mtt) && this.assembly.subtypeOf(mtt, geninfo.argflowtype);
            })
            .map((tt) => tt[1]);

        const rtype = this.typegen.getSMTTypeFor(geninfo.resulttype);
        let ops = tentities.map((tt) => {
            const mtt = MIRType.createSingle(tt);
            const test = new SMTCall(this.registerRequiredTypeCheck(geninfo.argflowtype, mtt), [new SMTVar("arg")]);

            const argpp = this.typegen.coerce(new SMTVar("arg"), geninfo.argflowtype, mtt);
            const pargs = geninfo.fields.map((field, i) => {
                const idxr = new SMTCall(this.typegen.generateEntityFieldGetFunction(geninfo.argflowtype.options[0] as MIREntityType, field.fkey), [argpp]);
                return this.typegen.coerce(idxr, this.typegen.getMIRType(field.declaredType), (geninfo.resulttype.options[0] as MIREphemeralListType).entries[i]);
            });
            const action = new SMTCall(this.typegen.getSMTConstructorName(geninfo.resulttype).cons, pargs);

            return { test: test, result: action };
        });

        const orelse = ops[ops.length - 1].result;
        ops = ops.slice(0, ops.length - 1);

        return new SMTFunction(geninfo.inv, [{ vname: "arg", vtype: this.typegen.getSMTTypeFor(geninfo.argflowtype) }], undefined, rtype, new SMTCond(new SMTVar("arg"), ops, orelse));
    }

    constructor(assembly: MIRAssembly, smtasm: SMTAssembly, typegen: SMTTypeEmitter, level: VerifierLevel) {
        this.assembly = assembly;
        this.smtasm = smtasm;
        this.typegen = typegen;
        this.level = level;

        this.currentRType = typegen.getMIRType("NSCore::None");
    }

    generateTempName(): string {
        return `@tmpvar@${this.tmpvarctr++}`;
    }

    generateErrorCreate(sinfo: SourceInfo, rtype: MIRType): SMTExp {
        const errorinfo = `${this.currentFile} @ line ${sinfo.line} -- pos ${sinfo.pos}`;
        const errorid = `error#${this.smtasm.errorDefinitions.size}`;
        if (!this.smtasm.errorDefinitions.has(errorinfo)) {
            this.smtasm.errorDefinitions.set(errorinfo, new SMTErrorCode(errorid, this.currentFile, sinfo));
        }

        return this.typegen.generateResultTypeConstructorError(rtype, new SMTConst(errorid));
    }

    isSafeInvoke(idecl: MIRInvokeDecl): boolean {
        return idecl.attributes.includes("__safe") || idecl.attributes.includes("__assume_safe");
    }

    varStringToSMT(name: string): SMTVar {
        if (name === "$$return") {
            return new SMTVar("$$return");
        }
        else {
            return new SMTVar(this.typegen.mangle(name));
        }
    }

    varToSMTName(varg: MIRRegisterArgument): SMTVar {
        return this.varStringToSMT(varg.nameID);
    }

    globalToSMT(gval: MIRGlobalVariable): SMTConst {
        return new SMTConst(this.typegen.mangle(gval.gkey));
    }

    constantToSMT(cval: MIRConstantArgument): SMTExp {
        if (cval instanceof MIRConstantNone) {
            return new SMTConst("bsq_none@literal");
        }
        else if (cval instanceof MIRConstantTrue) {
            return new SMTConst("true");
        }
        else if (cval instanceof MIRConstantFalse) {
            return new SMTConst("false");
        }
        else if (cval instanceof MIRConstantInt) {
            return new SMTConst(cval.value.slice(0, cval.value.length - 1));
        }
        else if (cval instanceof MIRConstantNat) {
            return new SMTConst(cval.value.slice(0, cval.value.length - 1));
        }
        else if (cval instanceof MIRConstantBigInt) {
            return new SMTConst(cval.value.slice(0, cval.value.length - 1));
        }
        else if (cval instanceof MIRConstantBigNat) {
            return new SMTConst(cval.value.slice(0, cval.value.length - 1));
        }
        else if (cval instanceof MIRConstantRational) {
            if(this.level === "Strong") {
                return new SMTCall("BRationalUnary_UF", [new SMTConst("@cons"), new SMTConst("\"" + cval.value + "\"")]);
            }
            else {
                const spos = cval.value.indexOf("/");
                const num = new SMTConst(cval.value.slice(0, spos) + ".0");
                const denom = new SMTConst(cval.value.slice(spos + 1, cval.value.length - 1) + ".0");
                return new SMTCall("/", [num, denom]);
            }
        }
        else if (cval instanceof MIRConstantComplex) {
            return new SMTCall("BComplexUnary_UF", [new SMTConst("@cons"), new SMTConst("\"" + cval.rvalue + cval.ivalue + "\"")]);
        }
        else if (cval instanceof MIRConstantFloat) {
            if(this.level === "Strong" || (cval.value.includes("e") || cval.value.includes("E"))) {
                return new SMTCall("BFloatUnary_UF", [new SMTConst("@cons"), new SMTConst("\"" + cval.value + "\"")]);
            }
            else {
                const sv = cval.value.includes(".") ? cval.value.slice(0, cval.value.length - 1) : (cval.value.slice(0, cval.value.length - 1) + ".0");
                return new SMTConst(sv);
            }
        }
        else if (cval instanceof MIRConstantDecimal) {
            if(this.level === "Strong" || (cval.value.includes("e") || cval.value.includes("E"))) {
                return new SMTCall("BDecimalUnary_UF", [new SMTConst("@cons"), new SMTConst("\"" + cval.value + "\"")]);
            }
            else {
                const sv = cval.value.includes(".") ? cval.value.slice(0, cval.value.length - 1) : (cval.value.slice(0, cval.value.length - 1) + ".0");
                return new SMTConst(sv);
            }
        }
        else if (cval instanceof MIRConstantString) {
            if(this.level === "Strong") {
                let args: SMTExp[] = [];
                for(let i = 0; i < cval.value.length; ++i) {
                    args.push(new SMTCall("seq.unit", [new SMTConst(`(_ bv32 ${cval.value.charCodeAt(i)})`)]));
                }
                return new SMTCall("seq.++", args);
            }
            else {
                return new SMTConst(cval.value);
            }
        }
        else if (cval instanceof MIRConstantString) {
            if(this.level === "Strong") {
                let args: SMTExp[] = [];
                for(let i = 0; i < cval.value.length; ++i) {
                    args.push(new SMTCall("seq.unit", [new SMTConst(`(_ bv32 ${cval.value.charCodeAt(i)})`)]));
                }
                return new SMTCall("seq.++", args);
            }
            else {
                return new SMTConst(cval.value);
            }
        }
        else {
            assert(cval instanceof MIRConstantRegex);

            const rval = (cval as MIRConstantRegex).value;
            const ere = this.assembly.literalRegexs.findIndex((re) => re.restr === rval.restr);

            return new SMTCall("bsq_regex@cons", [new SMTConst(`${ere}`)]);
        }
    }

    argToSMT(arg: MIRArgument): SMTExp {
        if (arg instanceof MIRRegisterArgument) {
            return this.varToSMTName(arg);
        }
        else if(arg instanceof MIRGlobalVariable) {
            return this.globalToSMT(arg);
        }
        else {
            return this.constantToSMT(arg as MIRConstantArgument);
        }
    }

    generateNoneCheck(arg: MIRArgument, argtype: MIRType): SMTExp {
        if (this.typegen.isType(argtype, "NSCore::None")) {
            return new SMTConst("true");
        }
        else if (!this.assembly.subtypeOf(this.typegen.getMIRType("NScore::None"), argtype)) {
            return new SMTConst("false");
        }
        else {
            const trepr = this.typegen.getSMTTypeFor(argtype);
            if(trepr.isGeneralKeyType()) {
                return new SMTCall("=", [new SMTConst("BKey@none")]);
            }
            else {
                return new SMTCall("=", [new SMTConst("BTerm@none")]);
            }
        }
    }

    generateSomeCheck(arg: MIRArgument, argtype: MIRType): SMTExp {
        if (this.typegen.isType(argtype, "NSCore::None")) {
            return new SMTConst("false");
        }
        else if (!this.assembly.subtypeOf(this.typegen.getMIRType("NScore::None"), argtype)) {
            return new SMTConst("true");
        }
        else {
            const trepr = this.typegen.getSMTTypeFor(argtype);
            if(trepr.isGeneralKeyType()) {
                return new SMTCall("not", [new SMTCall("=", [new SMTConst("BKey@none")])]);
            }
            else {
                return new SMTCall("not", [new SMTCall("=", [new SMTConst("BTerm@none")])]);
            }
        }
    }

    processDeadFlow(op: MIRDeadFlow): SMTExp {
        return this.generateErrorCreate(op.sinfo, this.currentRType);
    }

    processAbort(op: MIRAbort): SMTExp {
        return this.generateErrorCreate(op.sinfo, this.currentRType);
    }

    processAssertCheck(op: MIRAssertCheck, continuation: SMTExp): SMTExp {
        const chkval = this.argToSMT(op.arg);
        const errorval = this.generateErrorCreate(op.sinfo, this.currentRType);
        
        return new SMTIf(chkval, continuation, errorval);
    }

    processLoadUnintVariableValue(op: MIRLoadUnintVariableValue, continuation: SMTExp): SMTExp {
        const ufcname = this.generateUFConstantForType(this.typegen.getMIRType(op.oftype));

        return new SMTConst(ufcname);
    }

    processDeclareGuardFlagLocation(op: MIRDeclareGuardFlagLocation) {
        this.pendingMask = this.pendingMask.filter((pm) => pm.maskname !== op.name);
    }

    processSetConstantGuardFlag(op: MIRSetConstantGuardFlag) {
        const pm = this.pendingMask.find((mm) => mm.maskname === op.name) as SMTMaskConstruct;
        pm.entries[op.position] = new SMTConst(op.flag ? "true" : "false");
    }

    processConvertValue(op: MIRConvertValue, continuation: SMTExp): SMTExp {
        xxxx;
    }
    
    processCheckNoError(op: MIRCheckNoError, continuation: SMTExp): SMTExp {
        xxxx;
    }

    processExtractResultOkValue(op: MIRExtractResultOkValue, continuation: SMTExp): SMTExp {
        xxxx;
    }

    processLoadConst(op: MIRLoadConst, continuation: SMTExp): SMTExp {
        return new SMTLet(this.varToSMTName(op.trgt).vname, this.argToSMT(op.src), continuation);
    }

    processLoadConstDataString(op: MIRLoadConstDataString, continuation: SMTExp): SMTExp {
        xxxx;
    }

    processTupleHasIndex(op: MIRTupleHasIndex, continuation: SMTExp): SMTExp {
        const argtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(op.arglayouttype));
        const accessTypeTag = argtype.isGeneralTermType() ? new SMTCall("GetTypeTag@BTerm", [this.argToSMT(op.arg)]) : new SMTCall("GetTypeTag@BKey", [this.argToSMT(op.arg)]);
        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCall("HasIndex@", [accessTypeTag, new SMTConst(`TupleIndexTag_${op.idx}`)]), continuation);
    }

    processRecordHasProperty(op: MIRRecordHasProperty, continuation: SMTExp): SMTExp {
        const argtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(op.arglayouttype));
        const accessTypeTag = argtype.isGeneralTermType() ? new SMTCall("GetTypeTag@BTerm", [this.argToSMT(op.arg)]) : new SMTCall("GetTypeTag@BKey", [this.argToSMT(op.arg)]);
        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCall("HasProperty@", [accessTypeTag, new SMTConst(`RecordPropertyTag_${op.pname}`)]), continuation);
    }

    processLoadTupleIndex(op: MIRLoadTupleIndex, continuation: SMTExp): SMTExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);

        if(op.isvirtual) {
            const icall = this.generateLoadVirtualTupleInvName(this.typegen.getMIRType(op.argflowtype), op.idx, this.typegen.getMIRType(op.resulttype), undefined);
            if(this.requiredLoadVirtualTupleIndex.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), idx: op.idx, resulttype: this.typegen.getMIRType(op.resulttype), guard: undefined };
                this.requiredLoadVirtualTupleIndex.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCall(icall, [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const idxr = new SMTCall(this.typegen.generateTupleIndexGetFunction(argflowtype.options[0] as MIRTupleType, op.idx), [argpp]);
            return new SMTLet(this.varToSMTName(op.trgt).vname, idxr, continuation);
        }
    }

    processLoadTupleIndexSetGuard(op: MIRLoadTupleIndexSetGuard, continuation: SMTExp): SMTExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);

        if(op.isvirtual) {
            const icall = this.generateLoadVirtualTupleInvName(this.typegen.getMIRType(op.argflowtype), op.idx, this.typegen.getMIRType(op.resulttype), op.guard);
            if(this.requiredLoadVirtualTupleIndex.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), idx: op.idx, resulttype: this.typegen.getMIRType(op.resulttype), guard: op.guard };
                this.requiredLoadVirtualTupleIndex.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const cc = new SMTCall(icall, [argpp]);

            const callbind = this.generateTempName();
            const smtcallvar = new SMTVar(callbind);
            let ncont: SMTExp = new SMTConst("[UNDEF]");

            if(op.guard instanceof MIRMaskGuard) {
                const pm = this.pendingMask.find((mm) => mm.maskname === (op.guard as MIRMaskGuard).gmask) as SMTMaskConstruct;
                pm.entries[(op.guard as MIRMaskGuard).gindex] = this.typegen.generateAccessWithSetGuardResultGetFlag(this.typegen.getMIRType(op.resulttype), smtcallvar);

                ncont = new SMTLet(this.varToSMTName(op.trgt).vname, this.typegen.generateAccessWithSetGuardResultGetValue(this.typegen.getMIRType(op.resulttype), smtcallvar), continuation);
            }
            else {
                ncont = new SMTLetMulti([
                    { vname: this.varToSMTName((op.guard as MIRArgGuard).greg as MIRRegisterArgument).vname, value: this.typegen.generateAccessWithSetGuardResultGetFlag(this.typegen.getMIRType(op.resulttype), smtcallvar) },
                    { vname: this.varToSMTName(op.trgt).vname, value: this.typegen.generateAccessWithSetGuardResultGetValue(this.typegen.getMIRType(op.resulttype), smtcallvar) }
                ], continuation);
            }

            return new SMTLet(callbind, cc, ncont);
        }
        else {
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const idxr = new SMTCall(this.typegen.generateTupleIndexGetFunction(argflowtype.options[0] as MIRTupleType, op.idx), [argpp]);

            if(op.guard instanceof MIRMaskGuard) {
                const pm = this.pendingMask.find((mm) => mm.maskname === (op.guard as MIRMaskGuard).gmask) as SMTMaskConstruct;
                pm.entries[(op.guard as MIRMaskGuard).gindex] = new SMTConst("true");

                return new SMTLet(this.varToSMTName(op.trgt).vname, idxr, continuation);
            }
            else {
                return new SMTLetMulti([
                    { vname: this.varToSMTName((op.guard as MIRArgGuard).greg as MIRRegisterArgument).vname, value: new SMTConst("true") },
                    { vname: this.varToSMTName(op.trgt).vname, value: idxr }
                ], continuation);
            }
        }
    }

    processLoadRecordProperty(op: MIRLoadRecordProperty, continuation: SMTExp): SMTExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);

        if(op.isvirtual) {
            const icall = this.generateLoadVirtualPropertyInvName(this.typegen.getMIRType(op.argflowtype), op.pname, this.typegen.getMIRType(op.resulttype), undefined);
            if(this.requiredLoadVirtualRecordProperty.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), pname: op.pname, resulttype: this.typegen.getMIRType(op.resulttype), guard: undefined };
                this.requiredLoadVirtualRecordProperty.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCall(icall, [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const idxr = new SMTCall(this.typegen.generateRecordPropertyGetFunction(argflowtype.options[0] as MIRRecordType, op.pname), [argpp]);
            return new SMTLet(this.varToSMTName(op.trgt).vname, idxr, continuation);
        }
    }

    processLoadRecordPropertySetGuard(op: MIRLoadRecordPropertySetGuard, continuation: SMTExp): SMTExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);

        if(op.isvirtual) {
            const icall = this.generateLoadVirtualPropertyInvName(this.typegen.getMIRType(op.argflowtype), op.pname, this.typegen.getMIRType(op.resulttype), op.guard);
            if(this.requiredLoadVirtualRecordProperty.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), pname: op.pname, resulttype: this.typegen.getMIRType(op.resulttype), guard: op.guard };
                this.requiredLoadVirtualRecordProperty.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const cc = new SMTCall(icall, [argpp]);

            const callbind = this.generateTempName();
            const smtcallvar = new SMTVar(callbind);
            let ncont: SMTExp = new SMTConst("[UNDEF]");

            if(op.guard instanceof MIRMaskGuard) {
                const pm = this.pendingMask.find((mm) => mm.maskname === (op.guard as MIRMaskGuard).gmask) as SMTMaskConstruct;
                pm.entries[(op.guard as MIRMaskGuard).gindex] = this.typegen.generateAccessWithSetGuardResultGetFlag(this.typegen.getMIRType(op.resulttype), smtcallvar);

                ncont = new SMTLet(this.varToSMTName(op.trgt).vname, this.typegen.generateAccessWithSetGuardResultGetValue(this.typegen.getMIRType(op.resulttype), smtcallvar), continuation);
            }
            else {
                ncont = new SMTLetMulti([
                    { vname: this.varToSMTName((op.guard as MIRArgGuard).greg as MIRRegisterArgument).vname, value: this.typegen.generateAccessWithSetGuardResultGetFlag(this.typegen.getMIRType(op.resulttype), smtcallvar) },
                    { vname: this.varToSMTName(op.trgt).vname, value: this.typegen.generateAccessWithSetGuardResultGetValue(this.typegen.getMIRType(op.resulttype), smtcallvar) }
                ], continuation);
            }

            return new SMTLet(callbind, cc, ncont);
        }
        else {
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const idxr = new SMTCall(this.typegen.generateRecordPropertyGetFunction(argflowtype.options[0] as MIRRecordType, op.pname), [argpp]);
            
            if(op.guard instanceof MIRMaskGuard) {
                const pm = this.pendingMask.find((mm) => mm.maskname === (op.guard as MIRMaskGuard).gmask) as SMTMaskConstruct;
                pm.entries[(op.guard as MIRMaskGuard).gindex] = new SMTConst("true");

                return new SMTLet(this.varToSMTName(op.trgt).vname, idxr, continuation);
            }
            else {
                return new SMTLetMulti([
                    { vname: this.varToSMTName((op.guard as MIRArgGuard).greg as MIRRegisterArgument).vname, value: new SMTConst("true") },
                    { vname: this.varToSMTName(op.trgt).vname, value: idxr }
                ], continuation);
            }
        }
    }

    processLoadField(op: MIRLoadField, continuation: SMTExp): SMTExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);

        if(op.isvirtual) {
            const icall = this.generateLoadVirtualFieldInvName(this.typegen.getMIRType(op.argflowtype), op.field, this.typegen.getMIRType(op.resulttype));
            if(this.requiredLoadVirtualEntityField.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), field: this.assembly.fieldDecls.get(op.field) as MIRFieldDecl, resulttype: this.typegen.getMIRType(op.resulttype) };
                this.requiredLoadVirtualEntityField.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCall(icall, [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const idxr = new SMTCall(this.typegen.generateEntityFieldGetFunction(argflowtype.options[0] as MIREntityType, op.field), [argpp]);
            return new SMTLet(this.varToSMTName(op.trgt).vname, idxr, continuation);
        }
    }

    processTupleProjectToEphemeral(op: MIRTupleProjectToEphemeral, continuation: SMTExp): SMTExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);
        const resulttype = this.typegen.getMIRType(op.epht);

        if(op.isvirtual) {
            const icall = this.generateProjectVirtualTupleInvName(this.typegen.getMIRType(op.argflowtype), op.indecies, this.typegen.getMIRType(op.epht));
            if(this.requiredProjectVirtualTupleIndex.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), indecies: op.indecies, resulttype: this.typegen.getMIRType(op.epht) };
                this.requiredProjectVirtualTupleIndex.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCall(icall, [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const pargs = op.indecies.map((idx, i) => {
                const idxr = new SMTCall(this.typegen.generateTupleIndexGetFunction(argflowtype.options[0] as MIRTupleType, idx), [argpp]);
                return this.typegen.coerce(idxr, (argflowtype.options[0] as MIRTupleType).entries[idx].type, (resulttype.options[0] as MIREphemeralListType).entries[i]);
            });

            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCall(this.typegen.getSMTConstructorName(resulttype).cons, pargs), continuation);
        }
    }

    processRecordProjectToEphemeral(op: MIRRecordProjectToEphemeral, continuation: SMTExp): SMTExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);
        const resulttype = this.typegen.getMIRType(op.epht);

        if(op.isvirtual) {
            const icall = this.generateProjectVirtualRecordInvName(this.typegen.getMIRType(op.argflowtype), op.properties, this.typegen.getMIRType(op.epht));
            if(this.requiredProjectVirtualRecordProperty.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), properties: op.properties, resulttype: this.typegen.getMIRType(op.epht) };
                this.requiredProjectVirtualRecordProperty.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCall(icall, [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const pargs = op.properties.map((pname, i) => {
                const idxr = new SMTCall(this.typegen.generateRecordPropertyGetFunction(argflowtype.options[0] as MIRRecordType, pname), [argpp]);
                return this.typegen.coerce(idxr, ((argflowtype.options[0] as MIRRecordType).entries.find((vv) => vv.name === pname) as MIRRecordTypeEntry).type, (resulttype.options[0] as MIREphemeralListType).entries[i]);
            });

            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCall(this.typegen.getSMTConstructorName(resulttype).cons, pargs), continuation);
        }
    }

    processEntityProjectToEphemeral(op: MIREntityProjectToEphemeral, continuation: SMTExp): SMTExp {
        const arglayouttype = this.typegen.getMIRType(op.arglayouttype);
        const argflowtype = this.typegen.getMIRType(op.argflowtype);
        const resulttype = this.typegen.getMIRType(op.epht);

        if(op.isvirtual) {
            const icall = this.generateProjectVirtualEntityInvName(this.typegen.getMIRType(op.argflowtype), op.fields, this.typegen.getMIRType(op.epht));
            if(this.requiredProjectVirtualEntityField.findIndex((vv) => vv.inv === icall) === -1) {
                const geninfo = { inv: icall, argflowtype: this.typegen.getMIRType(op.argflowtype), fields: op.fields.map((fkey) => this.assembly.fieldDecls.get(fkey) as MIRFieldDecl), resulttype: this.typegen.getMIRType(op.epht) };
                this.requiredProjectVirtualEntityField.push(geninfo);
            }
            
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCall(icall, [argpp]), continuation);
        }
        else {
            const argpp = this.typegen.coerce(this.argToSMT(op.arg), arglayouttype, argflowtype);
            const pargs = op.fields.map((fkey, i) => {
                const idxr = new SMTCall(this.typegen.generateEntityFieldGetFunction(argflowtype.options[0] as MIREntityType, fkey), [argpp]);
                return this.typegen.coerce(idxr, this.typegen.getMIRType((this.assembly.fieldDecls.get(fkey) as MIRFieldDecl).declaredType), (resulttype.options[0] as MIREphemeralListType).entries[i]);
            });

            return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCall(this.typegen.getSMTConstructorName(resulttype).cons, pargs), continuation);
        }
    }

    processTupleUpdate(op: MIRTupleUpdate, continuation: SMTExp): SMTExp {
    }

    processRecordUpdate(op: MIRRecordUpdate, continuation: SMTExp): SMTExp {
    }

    processEntityUpdate(op: MIREntityUpdate, continuation: SMTExp): SMTExp {
    }

    processLoadFromEpehmeralList(op: MIRLoadFromEpehmeralList, continuation: SMTExp): SMTExp {
        const argtype = this.typegen.getMIRType(op.argtype);
        const resulttype = this.typegen.getMIRType(op.resulttype);

        const idxr = new SMTCall(this.typegen.generateEphemeralListGetFunction(argtype.options[0] as MIREphemeralListType, op.idx), [this.argToSMT(op.arg)]);
        return new SMTLet(this.varToSMTName(op.trgt).vname, this.typegen.coerce(idxr, (argtype.options[0] as MIREphemeralListType).entries[op.idx], resulttype), continuation);
    }

    processMultiLoadFromEpehmeralList(op: MIRMultiLoadFromEpehmeralList, continuation: SMTExp): SMTExp {
        const eltype = this.typegen.getMIRType(op.argtype).options[0] as MIREphemeralListType;

        const assigns = op.trgts.map((asgn) => {
            const idxr = new SMTCall(this.typegen.generateEphemeralListGetFunction(eltype, asgn.pos), [this.argToSMT(op.arg)]);
            const cexp = this.typegen.coerce(idxr, eltype.entries[asgn.pos], this.typegen.getMIRType(asgn.oftype));

            return { vname: this.varToSMTName(asgn.into).vname, value: cexp };
        });

        return new SMTLetMulti(assigns, continuation);
    }

    processSliceEpehmeralList(op: MIRSliceEpehmeralList, continuation: SMTExp): SMTExp {
        const eltype = this.typegen.getMIRType(op.argtype).options[0] as MIREphemeralListType;
        const sltype = this.typegen.getMIRType(op.sltype).options[0] as MIREphemeralListType;

        const pargs = sltype.entries.map((sle, i) => new SMTCall(this.typegen.generateEphemeralListGetFunction(eltype, i), [this.argToSMT(op.arg)]));
        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCall(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.sltype)).cons, pargs), continuation);
    }

    processInvokeFixedFunction(op: MIRInvokeFixedFunction, continuation: SMTExp): SMTExp {
        let mask: SMTMaskConstruct | undefined = undefined;
        if(op.optmask !== undefined) {
            mask = new SMTMaskConstruct(op.optmask);
            this.pendingMask.push(mask);
        }

        const args = op.args.map((arg) => this.argToSMT(arg));
        const call = mask !== undefined ? new SMTCallWOptMask(this.typegen.mangle(op.mkey), args, mask) : new SMTCall(this.typegen.mangle(op.mkey), args);

        const invk = (this.assembly.invokeDecls.get(op.mkey) || this.assembly.primitiveInvokeDecls.get(op.mkey)) as MIRInvokeDecl;
        const rtype = this.typegen.getMIRType(invk.resultType);

        if(invk.attributes.includes("__safe") || invk.attributes.includes("__assume_safe")) {
            const gcall = op.guard !== undefined ? new SMTIf(this.generateBoolForGuard(op.guard.guard), call, this.generateAltForGuardStmt(op.guard.altvalue, rtype)) : call;
            return new SMTLet(this.varToSMTName(op.trgt).vname, gcall, continuation);
        }
        else {
            const cres = this.generateTempName();
            const gcall = op.guard !== undefined ? new SMTIf(this.generateBoolForGuard(op.guard.guard), call, this.typegen.generateResultTypeConstructorSuccess(rtype, this.generateAltForGuardStmt(op.guard.altvalue, rtype))) : call;
            
            const okpath = new SMTLet(this.varToSMTName(op.trgt).vname, this.typegen.generateResultGetSuccess(rtype, gcall), continuation);
            const errpath = this.generateErrorCreate(op.sinfo, rtype);

            const icond = new SMTIf(this.typegen.generateResultIsErrorTest(rtype, new SMTVar(cres)), errpath, okpath);
            return new SMTLet(cres, gcall, icond);
        }
    }

    processInvokeVirtualFunction(op: MIRInvokeVirtualFunction, continuation: SMTExp): SMTExp {
        xxxx;
    }

    processInvokeVirtualOperator(op: MIRInvokeVirtualOperator, continuation: SMTExp): SMTExp {
        xxxx;
    }

    processConstructorTuple(op: MIRConstructorTuple, continuation: SMTExp): SMTExp {
        const args = op.args.map((arg) => this.argToSMT(arg));

        return new SMTCall(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultTupleType)).cons, args);
    }

    processConstructorTupleFromEphemeralList(op: MIRConstructorTupleFromEphemeralList, continuation: SMTExp): SMTExp {
        const elt = this.typegen.getMIRType(op.elistType).options[0] as MIREphemeralListType;
        const args = elt.entries.map((tt, i) => new SMTCall(this.typegen.generateEphemeralListGetFunction(elt, i), [this.argToSMT(op.arg)]));

        return new SMTCall(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultTupleType)).cons, args);
    }

    processConstructorRecord(op: MIRConstructorRecord, continuation: SMTExp): SMTExp {
        const args = op.args.map((arg) => this.argToSMT(arg[1]));

        return new SMTCall(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultRecordType)).cons, args);
    }

    processConstructorRecordFromEphemeralList(op: MIRConstructorRecordFromEphemeralList, continuation: SMTExp): SMTExp {
        const elt = this.typegen.getMIRType(op.elistType).options[0] as MIREphemeralListType;
        const eargs = elt.entries.map((tt, i) => new SMTCall(this.typegen.generateEphemeralListGetFunction(elt, i), [this.argToSMT(op.arg)]));

        const rtype = this.typegen.getMIRType(op.resultRecordType).options[0] as MIRRecordType;
        const args = rtype.entries.map((rentry) => {
            const eidx = op.propertyPositions.indexOf(rentry.name);
            return eargs[eidx];
        });

        return new SMTCall(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultRecordType)).cons, args);
    }

    processStructuredAppendTuple(op: MIRStructuredAppendTuple, continuation: SMTExp): SMTExp {
        let args: SMTExp[] = [];
        for (let i = 0; i < op.args.length; ++i) {
            const tt = this.typegen.getMIRType(op.ttypes[i].flow).options[0] as MIRTupleType;
            const argi = this.argToSMT(op.args[i]);

            for (let j = 0; j < tt.entries.length; ++j) {
                args.push(new SMTCall(this.typegen.generateTupleIndexGetFunction(tt, j), [argi]));
            }
        }

        return new SMTCall(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultTupleType)).cons, args);
    }

    processStructuredJoinRecord(op: MIRStructuredJoinRecord, continuation: SMTExp): SMTExp {
        const rtype = this.typegen.getMIRType(op.resultRecordType).options[0] as MIRRecordType;

        let args: SMTExp[] = [];
        for (let i = 0; i < op.args.length; ++i) {
            const tt = this.typegen.getMIRType(op.ttypes[i].flow).options[0] as MIRRecordType;
            const argi = this.argToSMT(op.args[i]);

            for (let j = 0; j < tt.entries.length; ++j) {
                const ppidx = rtype.entries.findIndex((ee) => ee.name === tt.entries[j].name);
                args[ppidx] = new SMTCall(this.typegen.generateRecordPropertyGetFunction(tt, tt.entries[j].name), [argi]);
            }
        }

        return new SMTCall(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultRecordType)).cons, args);
    }

    processConstructorEphemeralList(op: MIRConstructorEphemeralList, continuation: SMTExp): SMTExp {
        const args = op.args.map((arg) => this.argToSMT(arg));

        return new SMTCall(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultEphemeralListType)).cons, args);
    }

    processEphemeralListExtend(op: MIREphemeralListExtend, continuation: SMTExp): SMTExp {
        const ietype = this.typegen.getMIRType(op.argtype).options[0] as MIREphemeralListType;
        const iargs = ietype.entries.map((ee, i) => new SMTCall(this.typegen.generateEphemeralListGetFunction(ietype, i), [this.argToSMT(op.arg)]));

        const eargs = op.ext.map((arg) => this.argToSMT(arg));

        return new SMTCall(this.typegen.getSMTConstructorName(this.typegen.getMIRType(op.resultType)).cons, [...iargs, ...eargs]);
    }

    processConstructorPrimaryCollectionEmpty(op: MIRConstructorPrimaryCollectionEmpty, continuation: SMTExp): SMTExp {
        xxxx;
    }

    processConstructorPrimaryCollectionSingletons(op: MIRConstructorPrimaryCollectionSingletons, continuation: SMTExp): SMTExp {
        xxxx;
    }

    processConstructorPrimaryCollectionCopies(op: MIRConstructorPrimaryCollectionCopies, continuation: SMTExp): SMTExp {
        xxxx;
    }

    processConstructorPrimaryCollectionMixed(op: MIRConstructorPrimaryCollectionMixed, continuation: SMTExp): SMTExp {
        xxxx;
    }

    processBinKeyEq(op: MIRBinKeyEq, continuation: SMTExp): SMTExp {
        const lhs = this.typegen.coerceToKey(this.argToSMT(op.lhs), this.typegen.getMIRType(op.lhslayouttype));
        const rhs = this.typegen.coerceToKey(this.argToSMT(op.rhs), this.typegen.getMIRType(op.rhslayouttype));

        const eqcmp = new SMTCall("=", [lhs, rhs]);
        return new SMTLet(this.varToSMTName(op.trgt).vname, eqcmp, continuation);
    }

    processBinKeyLess(op: MIRBinKeyLess, continuation: SMTExp): SMTExp {
        xxxx;
    }

    processPrefixNotOp(op: MIRPrefixNotOp, continuation: SMTExp): SMTExp {
        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCall("not", [this.argToSMT(op.arg)]), continuation);
    }

    processAllTrue(op: MIRAllTrue, continuation: SMTExp): SMTExp {
        return new SMTLet(this.varToSMTName(op.trgt).vname, new SMTCall("and", [op.args.map((arg) => this.argToSMT(arg))]), continuation);
    }


    MIRIsTypeOf = "MIRIsTypeOf",

    MIRTempRegisterAssign = "MIRTempRegisterAssign",
    MIRParameterVarStore = "MIRParameterVarStore",
    MIRLocalVarStore = "MIRLocalVarStore",

    MIRReturnAssign = "MIRReturnAssign",
    MIRReturnAssignOfCons = "MIRReturnAssignOfCons"


    processOp(op: MIROp, continuation: SMTExp): SMTExp {
        xxxx;
    }

    generateAccessConstantValue(cp: MIRAccessConstantValue): SMTExp {
        const cdecl = this.assembly.constantDecls.get(cp.ckey) as MIRConstantDecl;

        const tv = this.generateTempName();
        const ivrtype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(cdecl.declaredType));
        const resulttype = this.typegen.getSMTTypeFor(this.currentRType);

        const constexp = new SMTValue(this.invokenameToSMT(cdecl.value));
        const checkerror = new SMTValue(`(is-result_error@${ivrtype} ${tv})`);
        const extracterror = (ivrtype !== resulttype) ? new SMTValue(`(result_error@${this.typegen.getSMTTypeFor(this.currentRType)} (result_error_code@${ivrtype} ${tv}))`) : new SMTValue(tv);
        const normalassign = new SMTLet(this.varToSMTName(cp.trgt), new SMTValue(`(result_success_value@${ivrtype} ${tv})`));

        return new SMTLet(tv, constexp, new SMTCond(checkerror, extracterror, normalassign));
    }

    generateMIRConstructorPrimary(cp: MIRConstructorPrimary): SMTExp {
        const ctype = this.assembly.entityDecls.get(cp.tkey) as MIREntityTypeDecl;
        const fvals = cp.args.map((arg, i) => {
            const ftype = this.typegen.getMIRType(ctype.fields[i].declaredType);
            return this.argToSMT(arg, ftype).emit();
        });

        const smtctype = this.typegen.generateEntityConstructor(cp.tkey);
        const cexp = ctype.fields.length === 0 ? new SMTValue(smtctype) : new SMTValue(`(${smtctype} ${fvals.join(" ")})`);
        return new SMTLet(this.varToSMTName(cp.trgt), cexp);
    }

    generateMIRConstructorPrimaryCollectionEmpty(cpce: MIRConstructorPrimaryCollectionEmpty): SMTExp {
        const cpcetype = this.typegen.getMIRType(cpce.tkey);
        const smtctype = this.typegen.generateEntityConstructor(cpce.tkey);
        
        if(this.typegen.typecheckIsName(cpcetype, /^NSCore::List<.*>$/)) {
            return new SMTLet(this.varToSMTName(cpce.trgt), new SMTValue(`(${smtctype} 0 ${this.typegen.generateEmptyDataArrayFor(cpce.tkey)})`));
        }
        else if(this.typegen.typecheckIsName(cpcetype, /^NSCore::Stack<.*>$/)) {
            return new SMTLet(this.varToSMTName(cpce.trgt), new SMTValue(`(${smtctype} 0 ${this.typegen.generateEmptyDataArrayFor(cpce.tkey)})`));
        }
        else if(this.typegen.typecheckIsName(cpcetype, /^NSCore::Queue<.*>$/)) {
            return new SMTLet(this.varToSMTName(cpce.trgt), new SMTValue(`(${smtctype} 0 0 ${this.typegen.generateEmptyDataArrayFor(cpce.tkey)})`));
        }
        else if(this.typegen.typecheckIsName(cpcetype, /^NSCore::Set<.*>$/) || this.typegen.typecheckIsName(cpcetype, /^NSCore::DynamicSet<.*>$/)) {
            return new SMTLet(this.varToSMTName(cpce.trgt), new SMTValue(`(${smtctype} 0 ${this.typegen.generateEmptyHasArrayFor(cpce.tkey)} bsqterm_none)`));
        }
        else {
           return new SMTLet(this.varToSMTName(cpce.trgt), new SMTValue(`(${smtctype} 0 ${this.typegen.generateEmptyHasArrayFor(cpce.tkey)} ${this.typegen.generateEmptyDataArrayFor(cpce.tkey)} bsqterm_none)`));
        }
    }

    generateMIRConstructorPrimaryCollectionSingletons(cpcs: MIRConstructorPrimaryCollectionSingletons): SMTExp {
        const cpcstype = this.typegen.getMIRType(cpcs.tkey);
        const smtctype = this.typegen.generateEntityConstructor(cpcs.tkey);

        if(this.typegen.typecheckIsName(cpcstype, /^NSCore::List<.*>$/)) {
            const oftype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
            let consv = this.typegen.generateEmptyDataArrayFor(cpcs.tkey);
            for (let i = 0; i < cpcs.args.length; ++i) {
                consv = `(store ${consv} ${i} ${this.argToSMT(cpcs.args[i], oftype).emit()})`;
            }

            return new SMTLet(this.varToSMTName(cpcs.trgt), new SMTValue(`(${smtctype} ${cpcs.args.length} ${consv})`));
        }
        else if(this.typegen.typecheckIsName(cpcstype, /^NSCore::Stack<.*>$/)) {
            const oftype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
            let consv = this.typegen.generateEmptyDataArrayFor(cpcs.tkey);
            for (let i = 0; i < cpcs.args.length; ++i) {
                consv = `(store ${consv} ${i} ${this.argToSMT(cpcs.args[i], oftype).emit()})`;
            }

            return new SMTLet(this.varToSMTName(cpcs.trgt), new SMTValue(`(${smtctype} ${cpcs.args.length} ${consv})`));
        }
        else if(this.typegen.typecheckIsName(cpcstype, /^NSCore::Queue<.*>$/)) {
            const oftype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
            let consv = this.typegen.generateEmptyDataArrayFor(cpcs.tkey);
            for (let i = 0; i < cpcs.args.length; ++i) {
                consv = `(store ${consv} ${i} ${this.argToSMT(cpcs.args[i], oftype).emit()})`;
            }

            return new SMTLet(this.varToSMTName(cpcs.trgt), new SMTValue(`(${smtctype} 0 ${cpcs.args.length} ${consv})`));
        }
        else if(this.typegen.typecheckIsName(cpcstype, /^NSCore::Set<.*>$/) || this.typegen.typecheckIsName(cpcstype, /^NSCore::DynamicSet<.*>$/)) {
            const oftype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("T") as MIRType;

            const kltype = [...this.typegen.assembly.entityDecls].find((edecl) => edecl[1].ns === "NSCore" && edecl[1].name === "KeyList" && (edecl[1].terms.get("K") as MIRType).trkey === oftype.trkey) as [string, MIREntityTypeDecl];
            const klcons = this.typegen.generateEntityConstructor(kltype[1].tkey);
            const klstore = this.typegen.getKeyListTypeForSet(this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl);

            let consv = `(${smtctype} %CTR% %HAS% %KEY%)`;
            for (let i = cpcs.args.length - 1; i >= 1; --i) {
                const arg = cpcs.args[i];

                const key = this.argToSMT(arg, oftype).emit();
                const ctrvar = this.generateTempName();
                const ctrup = `(ite (select %HAS% ${key}) %CTR% (+ %CTR% 1))`;

                const hasvar = this.generateTempName();
                const hasup = `(store %HAS% ${key} true)`;

                const keyvar = this.generateTempName();
                const keycons = `(${klcons} ${key} %KEY%)`;
                const keyforce = this.typegen.coerce(new SMTValue(keycons), this.typegen.getMIRType(kltype[1].tkey), klstore).emit();
                const keyup = `(ite (select %HAS% ${key}) %KEY% ${keyforce})`;

                const body = consv.replace(/%CTR%/g, ctrvar).replace(/%HAS%/g, hasvar).replace(/%KEY%/g, keyvar);
                consv = `(let ((${ctrvar} ${ctrup}) (${hasvar} ${hasup}) (${keyvar} ${keyup})) ${body})`
            }
            const key = this.argToSMT(cpcs.args[0], oftype).emit();
            const kl = new SMTValue(`(${klcons} ${key} bsqterm_none)`);
            const final = consv
                .replace(/%CTR%/g, "1")
                .replace(/%HAS%/g, `(store ${this.typegen.generateEmptyHasArrayFor(cpcs.tkey)} ${key} true)`)
                .replace(/%KEY%/g, this.typegen.coerce(kl, this.typegen.getMIRType(kltype[1].tkey), klstore).emit());

            return new SMTLet(this.varToSMTName(cpcs.trgt), new SMTValue(final));
        }
        else {
            const ktype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("K") as MIRType;
            const vtype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("V") as MIRType;

            const entrytype = [...this.typegen.assembly.entityDecls].find((edecl) => edecl[1].ns === "NSCore" && edecl[1].name === "MapEntry" && (edecl[1].terms.get("K") as MIRType).trkey === ktype.trkey && (edecl[1].terms.get("V") as MIRType).trkey === vtype.trkey) as [string, MIREntityTypeDecl];
            const entrykey = this.typegen.generateEntityAccessor(entrytype[1].tkey, (entrytype[1].fields.find((fd) => fd.name === "key") as MIRFieldDecl).fkey);
            const entryvalue = this.typegen.generateEntityAccessor(entrytype[1].tkey, (entrytype[1].fields.find((fd) => fd.name === "value") as MIRFieldDecl).fkey);

            const kltype = [...this.typegen.assembly.entityDecls].find((edecl) => edecl[1].ns === "NSCore" && edecl[1].name === "KeyList" && (edecl[1].terms.get("K") as MIRType).trkey === ktype.trkey) as [string, MIREntityTypeDecl];
            const klcons = this.typegen.generateEntityConstructor(kltype[1].tkey);
            const klstore = this.typegen.getKeyListTypeForMap(this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl);

            let consv = `(${smtctype} %CTR% %HAS% %ENTRYDATA% %KEY%)`;
            for (let i = cpcs.args.length - 1; i >= 1; --i) {
                const arg = cpcs.args[i];
                const entrykeyexp = `(${entrykey} ${this.argToSMT(arg, this.typegen.getMIRType(entrytype[1].tkey)).emit()})`;
                const entryvalexp = `(${entryvalue} ${this.argToSMT(arg, this.typegen.getMIRType(entrytype[1].tkey)).emit()})`;

                const key = entrykeyexp;
                const ctrvar = this.generateTempName();
                const ctrup = `(ite (select %HAS% ${key}) %CTR% (+ %CTR% 1))`;

                const hasvar = this.generateTempName();
                const hasup = `(store %HAS% ${key} true)`;

                const entrydatavar = this.generateTempName();
                const entrydataup = `(store %ENTRYDATA% ${key} ${entryvalexp})`;

                const keyvar = this.generateTempName();
                const keycons = `(${klcons} ${key} %KEY%)`;
                const keyforce = this.typegen.coerce(new SMTValue(keycons), this.typegen.getMIRType(kltype[1].tkey), klstore).emit();
                const keyup = `(ite (select %HAS% ${key}) %KEY% ${keyforce})`;

                const body = consv.replace(/%CTR%/g, ctrvar).replace(/%HAS%/g, hasvar).replace(/%ENTRYDATA%/g, entrydatavar).replace(/%KEY%/g, keyvar);
                consv = `(let ((${ctrvar} ${ctrup}) (${hasvar} ${hasup}) (${entrydatavar} ${entrydataup})  (${keyvar} ${keyup})) ${body})`
            }
            const entrykeyexp0 = `(${entrykey} ${this.argToSMT(cpcs.args[0], this.typegen.getMIRType(entrytype[1].tkey)).emit()})`;
            const entryvalexp0 = `(${entryvalue} ${this.argToSMT(cpcs.args[0], this.typegen.getMIRType(entrytype[1].tkey)).emit()})`;

            const key = entrykeyexp0;
            const kl = new SMTValue(`(${klcons} ${key} bsqterm_none)`);
            const final = consv
                .replace(/%CTR%/g, "1")
                .replace(/%HAS%/g, `(store ${this.typegen.generateEmptyHasArrayFor(cpcs.tkey)} ${key} true)`)
                .replace(/%ENTRYDATA%/g, `(store ${this.typegen.generateEmptyDataArrayFor(cpcs.tkey)} ${key} ${entryvalexp0})`)
                .replace(/%KEY%/g, this.typegen.coerce(kl, this.typegen.getMIRType(kltype[1].tkey), klstore).emit());

            return new SMTLet(this.varToSMTName(cpcs.trgt), new SMTValue(final));
        }
    }

    generateEquals(op: string, lhsinfertype: MIRType, lhs: MIRArgument, rhsinfertype: MIRType, rhs: MIRArgument, isstrict: boolean): string {
        let coreop = "";
        if (isstrict) {
            coreop = `(= ${this.argToSMT(lhs, lhsinfertype).emit()} ${this.argToSMT(rhs, rhsinfertype).emit()})`;
        }
        else {
            coreop = `(= ${this.argToSMT(lhs, this.typegen.keyType).emit()} ${this.argToSMT(rhs, this.typegen.keyType).emit()})`;
        }

        return op === "!=" ? `(not ${coreop})` : coreop;
    }

    generateLess(lhsinfertype: MIRType, lhs: MIRArgument, rhsinfertype: MIRType, rhs: MIRArgument, isstrict: boolean): string {
        if (isstrict) {
            const tt = lhsinfertype;
            const argl = this.argToSMT(lhs, lhsinfertype).emit();
            const argr = this.argToSMT(rhs, rhsinfertype).emit();

            if (this.typegen.typecheckIsName(tt, /^NSCore::Bool$/)) {
                return "false";
            }
            else if (this.typegen.typecheckIsName(tt, /^NSCore::Bool$/)) {
                return `(and (not ${argl}) ${argr})`;
            }
            else if (this.typegen.typecheckIsName(tt, /^NSCore::Int$/)) {
                return `(< ${argl} ${argr})`;
            }
            else if (this.typegen.typecheckIsName(tt, /^NSCore::BigInt$/)) {
                return `(< ${argl} ${argr})`;
            }
            else if (this.typegen.typecheckIsName(tt, /^NSCore::String$/)) {
                return `(str.< ${argl}${argr})`;
            }
            else if (this.typegen.typecheckIsName(tt, /^NSCore::SafeString<.*>$/)) {
                return `(str.< (bsq_safestring_value ${argl}) (bsq_safestring_value ${argr}))`;
            }
            else if (this.typegen.typecheckIsName(tt, /^NSCore::StringOf<.*>$/)) {
                return `(str.< (bsq_stringof_value ${argl}) (bsq_stringof_value ${argr}))`;
            }
            else if (this.typegen.typecheckIsName(tt, /^NSCore::UUID$/)) {
                return ` (str.< (bsq_uuid_value ${argl}) (bsq_uuid_value ${argr}))`;
            }
            else if (this.typegen.typecheckIsName(tt, /^NSCore::LogicalTime$/)) {
                return `(< (bsq_logicaltime_value ${argl}) (bsq_logicaltime_value ${argr}))`;
            }
            else if (this.typegen.typecheckIsName(tt, /^NSCore::CryptoHash$/)) {
                return `(str.< (bsq_cryptohash ${argl}) (bsq_cryptohash ${argr}))`;
            }
            else if (this.typegen.typecheckEntityAndProvidesName(tt, this.typegen.enumtype)) {
                return `(< (bsq_enum_value ${argl}) (bsq_enum_value ${argr}))`;
            }
            else {
                //TODO: this should turn into a gas driven generation -- and do this for composite and simple
                const iddecl = this.assembly.entityDecls.get(tt.trkey) as MIREntityTypeDecl;
                if (iddecl.attributes.includes("identifier_simple")) {
                    return `(bsqkeyless_identitysimple MIRNominalTypeEnum_${this.typegen.mangleStringForSMT(tt.trkey)} ${argl} ${argr})`;
                }
                else {
                    return `(bsqkeyless_identitycompound MIRNominalTypeEnum_${this.typegen.mangleStringForSMT(tt.trkey)} ${argl} ${argr})`;
                }
            }
        }
        else {
            //TODO: this should turn into a gas driven generation
            return `(bsqkeyless ${this.argToSMT(lhs, this.typegen.keyType).emit()} ${this.argToSMT(rhs, this.typegen.keyType).emit()})`;
        }
    }

    generateCompare(op: string, lhsinfertype: MIRType, lhs: MIRArgument, rhsinfertype: MIRType, rhs: MIRArgument): string {
        if (op === "<") {
            return this.generateLess(lhsinfertype, lhs, rhsinfertype, rhs, true);
        }
        else if (op === "<=") {
            return `(or ${this.generateLess(lhsinfertype, lhs, rhsinfertype, rhs, true)} ${this.generateEquals("=", lhsinfertype, lhs, rhsinfertype, rhs, true)})`;
        }
        else if (op === ">") {
            return this.generateLess(rhsinfertype, rhs, lhsinfertype, lhs, true);
        }
        else {
            return `(or ${this.generateLess(rhsinfertype, rhs, lhsinfertype, lhs, true)} ${this.generateEquals("=", rhsinfertype, rhs, lhsinfertype, lhs, true)})`;
        }
    }

    generateStmt(op: MIROp, fromblck: string, gas: number | undefined): SMTExp | undefined {
        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const lcv = op as MIRLoadConst;
                return new SMTLet(this.varToSMTName(lcv.trgt), this.generateConstantExp(lcv.src, this.getArgType(lcv.trgt)));
            }
            case MIROpTag.MIRLoadConstSafeString: {
                return this.generateLoadConstSafeString(op as MIRLoadConstSafeString);
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
            case MIROpTag.MIRInvokeInvariantCheckDirect: {
                const icd = op as MIRInvokeInvariantCheckDirect;
                return this.generateMIRInvokeInvariantCheckDirect(icd);
            }
            case MIROpTag.MIRInvokeInvariantCheckVirtualTarget: {
                return NOT_IMPLEMENTED<SMTExp>("MIRInvokeInvariantCheckVirtualTarget");
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
                return new SMTLet(this.varToSMTName(af.trgt), this.generateMIRAccessFromFieldExpression(af.arg, this.typegen.getMIRType(af.argInferType), af.field, this.typegen.getMIRType(af.resultAccessType)));
            }
            case MIROpTag.MIRProjectFromFields: {
                const pf = op as MIRProjectFromFields;
                return this.generateMIRProjectFromFields(pf, this.typegen.getMIRType(pf.resultProjectType));
            }
            case MIROpTag.MIRProjectFromTypeTuple: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromTypeTuple");
            }
            case MIROpTag.MIRProjectFromTypeRecord: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromTypeRecord");
            }
            case MIROpTag.MIRProjectFromTypeNominal: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromTypeNominal");
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
                return this.generateMIRModifyWithFields(mf, this.typegen.getMIRType(mf.resultNominalType));
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
                return this.generateMIRStructuredExtendObject(so, this.typegen.getMIRType(so.resultNominalType));
            }
            case MIROpTag.MIRLoadFromEpehmeralList: {
                const le = op as MIRLoadFromEpehmeralList;
                return this.generateMIRLoadFromEpehmeralList(le);
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
                    return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`(not ${this.argToSMT(pfx.arg, this.typegen.boolType).emit()})`));
                }
                else {
                    if (pfx.op === "-") {
                        if (pfx.arg instanceof MIRConstantInt) {
                            return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`-${(pfx.arg as MIRConstantInt).value}`));
                        }
                        else if (pfx.arg instanceof MIRConstantBigInt) {
                            return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`-${(pfx.arg as MIRConstantBigInt).digits()}`));
                        }
                        else if (pfx.arg instanceof MIRConstantFloat64) {
                            return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`-${(pfx.arg as MIRConstantFloat64).digits()}`));
                        }
                        else {
                            const opt = this.getArgType(pfx.trgt);
                            if (this.typegen.typecheckIsName(opt, /^NSCore::Int$/)) {
                                return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`(* -1 ${this.argToSMT(pfx.arg, this.typegen.intType).emit()})`));
                            }
                            else if (this.typegen.typecheckIsName(opt, /^NSCore::BigInt$/)) {
                                return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`(* -1 ${this.argToSMT(pfx.arg, this.typegen.bigIntType).emit()})`));
                            }
                            else {
                                return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`(* -1.0 ${this.argToSMT(pfx.arg, this.typegen.float64Type).emit()})`));
                            }
                        }
                    }
                    else {
                        return new SMTLet(this.varToSMTName(pfx.trgt), this.argToSMT(pfx.arg, this.getArgType(pfx.trgt)));
                    }
                }
            }
            case MIROpTag.MIRBinOp: {
                const bop = op as MIRBinOp;
                const opt = this.getArgType(bop.trgt);

                if (this.typegen.typecheckIsName(opt, /^NSCore::Int$/)) {
                    const chk = new SMTCond(new SMTValue(`(@int_unsafe ${this.varToSMTName(bop.trgt)})`), this.generateErrorCreate(bop.sinfo, this.typegen.getSMTTypeFor(this.currentRType)), SMTFreeVar.generate());
                    const opp = new SMTLet(this.varToSMTName(bop.trgt), new SMTValue(`(${bop.op} ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`), chk);
                    if(bop.op !== "/") {
                        return opp;
                    }
                    else {
                        return new SMTCond(new SMTValue(`(= ${this.argToSMT(bop.rhs, this.typegen.intType).emit()} 0)`), this.generateErrorCreate(op.sinfo, this.typegen.getSMTTypeFor(this.currentRType)), opp);
                    }
                }
                else if (this.typegen.typecheckIsName(opt, /^NSCore::BigInt$/)) {
                    const opp = new SMTLet(this.varToSMTName(bop.trgt), new SMTValue(`(${bop.op} ${this.argToSMT(bop.lhs, this.typegen.bigIntType).emit()} ${this.argToSMT(bop.rhs, this.typegen.bigIntType).emit()})`));
                    if(bop.op !== "/") {
                        return opp;
                    }
                    else {
                        return new SMTCond(new SMTValue(`(= ${this.argToSMT(bop.rhs, this.typegen.intType).emit()} 0)`), this.generateErrorCreate(op.sinfo, this.typegen.getSMTTypeFor(this.currentRType)), opp);
                    }
                }
                else {
                    return new SMTLet(this.varToSMTName(bop.trgt), new SMTValue(`(${bop.op} ${this.argToSMT(bop.lhs, this.typegen.float64Type).emit()} ${this.argToSMT(bop.rhs, this.typegen.float64Type).emit()})`));
                }
            }
            case MIROpTag.MIRBinEq: {
                const beq = op as MIRBinEq;

                const lhvtypeinfer = this.typegen.getMIRType(beq.lhsInferType);
                const rhvtypeinfer = this.typegen.getMIRType(beq.rhsInferType);
                return new SMTLet(this.varToSMTName(beq.trgt), new SMTValue(this.generateEquals(beq.op, lhvtypeinfer, beq.lhs, rhvtypeinfer, beq.rhs, !beq.relaxed)));
            }
            case MIROpTag.MIRBinLess: {
                const blt = op as MIRBinLess;

                const lhvtypeinfer = this.typegen.getMIRType(blt.lhsInferType);
                const rhvtypeinfer = this.typegen.getMIRType(blt.rhsInferType);
                return new SMTLet(this.varToSMTName(blt.trgt), new SMTValue(this.generateLess(lhvtypeinfer, blt.lhs, rhvtypeinfer, blt.rhs, !blt.relaxed)));
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
                const infertype = this.typegen.getMIRType(top.argInferType);

                return new SMTLet(this.varToSMTName(top.trgt), new SMTValue(this.generateTypeCheck(this.argToSMT(top.arg, infertype).emit(), argtype, infertype, oftype)));
            }
            case MIROpTag.MIRRegAssign: {
                const regop = op as MIRRegAssign;
                return new SMTLet(this.varToSMTName(regop.trgt), this.argToSMT(regop.src, this.getArgType(regop.trgt)));
            }
            case MIROpTag.MIRTruthyConvert: {
                const tcop = op as MIRTruthyConvert;
                return new SMTLet(this.varToSMTName(tcop.trgt), this.generateTruthyConvert(tcop.src));
            }
            case MIROpTag.MIRVarStore: {
                const vsop = op as MIRVarStore;
                return new SMTLet(this.varToSMTName(vsop.name), this.argToSMT(vsop.src, this.getArgType(vsop.name)));
            }
            case MIROpTag.MIRPackSlice: {
                const vps = op as MIRPackSlice;
                return this.generateMIRPackSlice(vps);
            }
            case MIROpTag.MIRPackExtend: {
                const vpe = op as MIRPackExtend;
                return this.generateMIRPackSliceExtend(vpe);
            }
            case MIROpTag.MIRReturnAssign: {
                const raop = op as MIRReturnAssign;
                return new SMTLet(this.varToSMTName(raop.name), this.argToSMT(raop.src, this.getArgType(raop.name)));
            }
            case MIROpTag.MIRAbort: {
                const aop = (op as MIRAbort);
                return this.generateErrorCreate(aop.sinfo, this.typegen.getSMTTypeFor(this.currentRType));
            }
            case MIROpTag.MIRDebug: {
                return undefined;
            }
            case MIROpTag.MIRJump: {
                return undefined;
            }
            case MIROpTag.MIRJumpCond: {
                const cjop = op as MIRJumpCond;
                return new SMTCond(this.argToSMT(cjop.arg, this.typegen.boolType), SMTFreeVar.generate("#true_trgt#"), SMTFreeVar.generate("#false_trgt#"));
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

    generateBlockExps(issafe: boolean, block: MIRBasicBlock, fromblock: string, blocks: Map<string, MIRBasicBlock>, gas: number | undefined): SMTExp {
        const exps: SMTExp[] = [];
        for (let i = 0; i < block.ops.length; ++i) {
            const exp = this.generateStmt(block.ops[i], fromblock, gas);
            if (exp !== undefined) {
                exps.push(exp);
            }
        }

        if (block.label === "exit") {
            const resulttype = this.typegen.getSMTTypeFor(this.currentRType);
            let rexp = issafe ? new SMTValue("$$return") : new SMTValue(`(result_success@${resulttype} $$return)`) as SMTExp;
            for (let i = exps.length - 1; i >= 0; --i) {
                rexp = exps[i].bind(rexp, "#body#");
            }

            return rexp;
        }
        else {
            const jop = block.ops[block.ops.length - 1];
            if(jop.tag === MIROpTag.MIRAbort) {
                let rexp = exps[exps.length - 1];
                for (let i = exps.length - 2; i >= 0; --i) {
                    rexp = exps[i].bind(rexp, "#body#");
                }

                return rexp;
            }
            else if (jop.tag === MIROpTag.MIRJump) {
                let rexp = this.generateBlockExps(issafe, blocks.get((jop as MIRJump).trgtblock) as MIRBasicBlock, block.label, blocks, gas);
                for (let i = exps.length - 1; i >= 0; --i) {
                    rexp = exps[i].bind(rexp, "#body#");
                }

                return rexp;
            }
            else {
                assert(jop.tag === MIROpTag.MIRJumpCond || jop.tag === MIROpTag.MIRJumpNone);

                let tblock = ((jop.tag === MIROpTag.MIRJumpCond) ? blocks.get((jop as MIRJumpCond).trueblock) : blocks.get((jop as MIRJumpNone).noneblock)) as MIRBasicBlock;
                let texp = this.generateBlockExps(issafe, tblock, block.label, blocks, gas);

                let fblock = ((jop.tag === MIROpTag.MIRJumpCond) ? blocks.get((jop as MIRJumpCond).falseblock) : blocks.get((jop as MIRJumpNone).someblock)) as MIRBasicBlock;
                let fexp = this.generateBlockExps(issafe, fblock, block.label, blocks, gas);

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

        const args = idecl.params.map((arg) => `(${this.varNameToSMTName(arg.name)} ${this.typegen.getSMTTypeFor(this.typegen.getMIRType(arg.type))})`);
        const restype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(idecl.resultType));

        const issafe = this.isSafeInvoke(idecl);

        const decl = issafe
            ? `(define-fun ${this.invokenameToSMT(idecl.key)} (${args.join(" ")}) ${restype}`
            : `(define-fun ${this.invokenameToSMT(idecl.key)}${gas !== undefined ? `@gas${gas}` : ""} (${args.join(" ")}) Result@${restype}`;

        if (idecl instanceof MIRInvokeBodyDecl) {
            this.vtypes = new Map<string, MIRType>();
            (idecl.body.vtypes as Map<string, string>).forEach((tkey, name) => {
                this.vtypes.set(name, this.typegen.getMIRType(tkey));
            });

            const blocks = (idecl as MIRInvokeBodyDecl).body.body;
            const body = this.generateBlockExps(issafe, blocks.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocks, gasdown);

            return `${decl} \n${body.emit("  ")})`;

        }
        else {
            assert(idecl instanceof MIRInvokePrimitiveDecl);

            const params = idecl.params.map((arg) => this.varNameToSMTName(arg.name));
            return `${decl} \n  ${this.generateBuiltinBody(issafe, idecl as MIRInvokePrimitiveDecl, params).emit("  ")}\n)`;
        }
    }

    generateBuiltinBody(issafe: boolean, idecl: MIRInvokePrimitiveDecl, params: string[]): SMTExp {
        const rtype = this.typegen.getMIRType(idecl.resultType);

        let bodyres: SMTExp | undefined = undefined;
        const enclkey = (idecl.enclosingDecl || "[NA]") as MIRNominalTypeKey
        switch (idecl.implkey) {
            case "validator_accepts": {
                const rs = this.assembly.literalRegexs.get(this.assembly.validatorRegexs.get(idecl.enclosingDecl as MIRNominalTypeKey) as string) as MIRRegex;
                bodyres = compileRegexSMTMatch(rs, params[0]);
                break;
            }
            case "enum_create": {
                bodyres = new SMTValue(`(bsq_enum@cons MIRNominalTypeEnum_${this.typegen.mangleStringForSMT(enclkey)} ${params[0]})`);
                break;
            }
            case "idkey_from_simple": {
                const kv = this.typegen.coerce(new SMTValue(params[0]), this.typegen.getMIRType(idecl.params[0].type), this.typegen.keyType).emit();
                bodyres = new SMTValue(`(bsq_idkeysimple@cons MIRNominalTypeEnum_${this.typegen.mangleStringForSMT(enclkey)} ${kv})`);
                break;
            }
            case "idkey_from_composite": {
                let kvs: string = "bsqidkey_array_empty";
                for (let i = 0; i < params.length; ++i) {
                    const select = this.typegen.coerce(new SMTValue(params[i]), this.typegen.getMIRType(idecl.params[i].type), this.typegen.keyType);
                    kvs = `(store ${kvs} ${i} ${select.emit()})`;
                }
                
                bodyres = new SMTValue(`(bsq_idkeycompound@cons MIRNominalTypeEnum_${this.typegen.mangleStringForSMT(enclkey)} ${kvs})`);
                break;
            }
            case "string_count": {
                bodyres = new SMTValue(`(str.len ${params[0]})`);
                break;
            }
            case "string_charat": {
                bodyres = new SMTValue(`(str.at ${params[0]} ${params[1]})`);
                break;
            }
            case "string_concat": {
                bodyres = new SMTValue(`(str.++ ${params[0]} ${params[1]})`);
                break;
            }
            case "string_substring": {
                bodyres = new SMTValue(`(str.substr ${params[0]} ${params[1]} ${params[2]})`);
                break;
            }
            case "safestring_string": {
                bodyres = new SMTValue(`(bsq_safestring_value ${params[0]})`);
                break;
            }
            case "safestring_unsafe_from": {
                bodyres = new SMTValue(`(bsq_safestring@cons MIRNominalTypeEnum_${this.typegen.mangleStringForSMT(enclkey)} ${params[0]})`);
                break;
            }
            case "stringof_string": {
                bodyres = new SMTValue(`(bsq_stringof_value ${params[0]})`);
                break;
            }
            case "stringof_unsafe_from": {
                bodyres = new SMTValue(`(bsq_stringof@cons MIRNominalTypeEnum_${this.typegen.mangleStringForSMT(enclkey)} ${params[0]})`);
                break;
            }
            case "list_size": {
                bodyres = this.typegen.generateSpecialTypeFieldAccessExp(enclkey, "size", params[0]);
                break;
            }
            case "list_unsafe_get": {
                bodyres = new SMTValue(`(select ${this.typegen.generateSpecialTypeFieldAccess(enclkey, "entries", params[0])} ${params[1]})`);
                break;
            }
            case "list_unsafe_push": {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const entries = this.typegen.generateSpecialTypeFieldAccess(enclkey, "entries", params[0]);
                const csize = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                bodyres = new SMTValue(`(${cons} (+ ${csize} 1) (store ${entries} ${csize} ${params[1]}))`);
                break;
            }
            case "list_unsafe_set": {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const entries = this.typegen.generateSpecialTypeFieldAccess(enclkey, "entries", params[0]);
                const csize = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                bodyres = new SMTValue(`(${cons} ${csize} (store ${entries} ${params[1]} ${params[2]}))`);
                break;
            }
            case "set_size": {
                bodyres = this.typegen.generateSpecialTypeFieldAccessExp(enclkey, "size", params[0]);
                break;
            }
            case "set_has_key": {
                bodyres = new SMTValue(`(select ${this.typegen.generateSpecialTypeFieldAccess(enclkey, "has", params[0])} ${params[1]})`)
                break;
            }
            case "set_get_keylist": {
                bodyres = this.typegen.generateSpecialTypeFieldAccessExp(enclkey, "keylist", params[0]);
                break;
            }
            case "set_unsafe_add":  {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const size = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                const has = this.typegen.generateSpecialTypeFieldAccess(enclkey, "has", params[0]);
                const klctype = this.typegen.getKeyListTypeForSet(this.typegen.assembly.entityDecls.get(enclkey) as MIREntityTypeDecl);
                const kll = this.typegen.coerce(new SMTValue(params[2]), this.typegen.getMIRType(idecl.params[2].type), klctype);
                bodyres = new SMTValue(`(${cons} (+ ${size} 1) (store ${has} ${params[1]} true) ${kll.emit()})`);
                break;
            }
            case "map_size": {
                bodyres = this.typegen.generateSpecialTypeFieldAccessExp(enclkey, "size", params[0]);
                break;
            }
            case "map_has_key": {
                bodyres = new SMTValue(`(select ${this.typegen.generateSpecialTypeFieldAccess(enclkey, "has", params[0])} ${params[1]})`)
                break;
            }
            case "map_at_val": {
                bodyres = new SMTValue(`(select ${this.typegen.generateSpecialTypeFieldAccess(enclkey, "values", params[0])} ${params[1]})`);
                break;
            }
            case "map_get_keylist": {
                bodyres = this.typegen.generateSpecialTypeFieldAccessExp(enclkey, "keylist", params[0]);
                break;
            }
            case "map_keyset": {
                const cons = this.typegen.generateEntityConstructor(idecl.resultType);
                const size = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                const has = this.typegen.generateSpecialTypeFieldAccess(enclkey, "has", params[0]);
                const keylist = this.typegen.generateSpecialTypeFieldAccess(enclkey, "keylist", params[0]);
                bodyres = new SMTValue(`(${cons} ${size} ${has} ${keylist})`);
                break;
            }
            case "map_unsafe_add": {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const size = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                const has = this.typegen.generateSpecialTypeFieldAccess(enclkey, "has", params[0]);
                const entries = this.typegen.generateSpecialTypeFieldAccess(enclkey, "values", params[0]);
                const klctype = this.typegen.getKeyListTypeForMap(this.typegen.assembly.entityDecls.get(enclkey) as MIREntityTypeDecl);
                const kll = this.typegen.coerce(new SMTValue(params[3]), this.typegen.getMIRType(idecl.params[3].type), klctype);
                bodyres = new SMTValue(`(${cons} (+ ${size} 1) (store ${has} ${params[1]} true) (store ${entries} ${params[1]} ${params[2]}) ${kll.emit()})`);
                break;
            }
            case "map_unsafe_update": {
                const cons = this.typegen.generateEntityConstructor(enclkey);
                const size = this.typegen.generateSpecialTypeFieldAccess(enclkey, "size", params[0]);
                const has = this.typegen.generateSpecialTypeFieldAccess(enclkey, "has", params[0]);
                const entries = this.typegen.generateSpecialTypeFieldAccess(enclkey, "values", params[0]);
                const kl = this.typegen.generateSpecialTypeFieldAccess(enclkey, "keylist", params[0]);
                bodyres = new SMTValue(`(${cons} ${size} ${has} (store ${entries} ${params[1]} ${params[2]}) ${kl})`);
                break;
            }
            default: {
                const pctag = [...idecl.pcodes].map((pc) => this.typegen.mangleStringForSMT(pc[1].code)).join("$");
                const fname = `@${idecl.implkey}` + (pctag.length !== 0 ? `$${pctag}` : "");
                const pdecls = idecl.params.map((p) => this.typegen.getSMTTypeFor(this.typegen.getMIRType(p.type)));
                const udecl = `(declare-fun ${fname} (${pdecls.join(" ")}) ${this.typegen.getSMTTypeFor(this.typegen.getMIRType(idecl.resultType))})`;
                
                this.uninterpDecl.add(udecl);
                this.generateBuiltinAxioms(fname, idecl, params);

                bodyres = new SMTValue(params.length === 0 ? `(${fname})` : `(${fname} ${params.join(" ")})`);
                break;
            }
        }

        return issafe ? new SMTValue(bodyres.emit()) : new SMTValue(`(result_success@${this.typegen.getSMTTypeFor(rtype)} ${bodyres.emit()})`);
    }

    isAxiomLevelEnabled(lvl: AxiomLevel): boolean {
        if (this.axiomgen === AxiomLevel.none) {
            return false;
        }
        else if (this.axiomgen === AxiomLevel.basic) {
            return lvl === AxiomLevel.basic;
        }
        else if (this.axiomgen === AxiomLevel.standard) {
            return lvl === AxiomLevel.basic || this.axiomgen === AxiomLevel.standard;
        }
        else {
            return true;
        }
    }

    createLambdaForPred(pc: MIRPCode, ...args: string[]): string {
        const cargs = pc.cargs.map((ca) => this.typegen.mangleStringForSMT(ca));

        return (args.length + cargs.length === 0) ? `(result_success_value@Bool (${this.typegen.mangleStringForSMT(pc.code)}))` : `(result_success_value@Bool (${this.typegen.mangleStringForSMT(pc.code)} ${[...args, ...cargs].join(" ")}))`;
    }

    generateBuiltinAxioms(fname: string, idecl: MIRInvokePrimitiveDecl, params: string[]) {
        const enclkey = (idecl.enclosingDecl || "[NA]") as MIRNominalTypeKey

        switch (idecl.implkey) {
            case "list_all": {
                const ltype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(idecl.enclosingDecl as string));
                const lsize = this.typegen.generateSpecialTypeFieldAccessExp(enclkey, "size", "l");
                const larr = this.typegen.generateSpecialTypeFieldAccessExp(enclkey, "entries", "l");

                if(this.isAxiomLevelEnabled(AxiomLevel.basic)) {
                    this.insertAxioms(
                        `(assert (forall ((l ${ltype})) (=> (= ${lsize.emit()} 0) (${fname} l))))`
                    );
                }
                if(this.isAxiomLevelEnabled(AxiomLevel.standard)) {
                    const lambda = this.createLambdaForPred(idecl.pcodes.get("p") as MIRPCode, `(select ${larr.emit()} i)`)
                    this.insertAxioms(
                        `(assert (forall ((l ${ltype}) (i Int)) (=> (${fname} l) ${lambda})))`
                    );
                }
                if(this.isAxiomLevelEnabled(AxiomLevel.full)) { 
                }
                break;
            }
            case "list_none": {
                const ltype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(idecl.enclosingDecl as string));
                const lsize = this.typegen.generateSpecialTypeFieldAccessExp(enclkey, "size", "l");
                const larr = this.typegen.generateSpecialTypeFieldAccessExp(enclkey, "entries", "l");

                if(this.isAxiomLevelEnabled(AxiomLevel.basic)) {
                    this.insertAxioms(
                        `(assert (forall ((l ${ltype})) (=> (= ${lsize.emit()} 0) (${fname} l))))`
                    );
                }
                if(this.isAxiomLevelEnabled(AxiomLevel.standard)) {
                    const lambda = this.createLambdaForPred(idecl.pcodes.get("p") as MIRPCode, `(select ${larr.emit()} i)`)
                    this.insertAxioms(
                        `(assert (forall ((l ${ltype}) (i Int)) (=> (${fname} l) (not ${lambda}))))`
                    );
                }
                if(this.isAxiomLevelEnabled(AxiomLevel.full)) { 
                }
                break;
            }
            case "list_any": {
                const ltype = this.typegen.getSMTTypeFor(this.typegen.getMIRType(idecl.enclosingDecl as string));
                const lsize = this.typegen.generateSpecialTypeFieldAccessExp(enclkey, "size", "l");

                if(this.isAxiomLevelEnabled(AxiomLevel.basic)) {
                    this.insertAxioms(
                        `(assert (forall ((l ${ltype})) (=> (= ${lsize.emit()} 0) (not (${fname} l)))))`
                    );
                }
                if(this.isAxiomLevelEnabled(AxiomLevel.standard)) {
                }
                if(this.isAxiomLevelEnabled(AxiomLevel.full)) { 
                }
                break;
            }
            default: {
                assert(false, `Need to implement -- ${idecl.iname}`);
                break;
            }
        }
    }

    insertAxioms(...axioms: string[]) {
        axioms.forEach((ax) => this.uninterpAxioms.add(ax));
    }
}

const UninterpFunctions: string =
`
`;

export {
    AxiomLevel, SMTBodyEmitter, UninterpFunctions
};
