//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIRTypeOption, MIRInvokeDecl, MIRInvokeBodyDecl, MIRInvokePrimitiveDecl } from "../../compiler/mir_assembly";
import { CPPTypeEmitter } from "./cpptype_emitter";
import { sanitizeForCpp, NOT_IMPLEMENTED, isInlinableType, getInlinableType, isUniqueEntityType, filenameClean } from "./cpputils";
import { MIRArgument, MIRRegisterArgument, MIRConstantNone, MIRConstantFalse, MIRConstantTrue, MIRConstantInt, MIRConstantArgument, MIRConstantString, MIROp, MIROpTag, MIRLoadConst, MIRAccessArgVariable, MIRAccessLocalVariable, MIRInvokeFixedFunction, MIRPrefixOp, MIRBinOp, MIRBinEq, MIRBinCmp, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRRegAssign, MIRTruthyConvert, MIRLogicStore, MIRVarStore, MIRReturnAssign, MIRDebug, MIRJump, MIRJumpCond, MIRJumpNone, MIRAbort, MIRBasicBlock, MIRPhi } from "../../compiler/mir_ops";
import * as assert from "assert";
import { topologicalOrder } from "../../compiler/mir_info";

class CPPBodyEmitter {
    readonly assembly: MIRAssembly;
    readonly typegen: CPPTypeEmitter;

    readonly allPropertyNames: Set<string> = new Set<string>();
    readonly allConstStrings: Map<string, string> = new Map<string, string>();

    private currentFile: string = "[No File]";
    private currentRType: MIRType;
    private scopectr: number = 0;

    private vtypes: Map<string, MIRType> = new Map<string, MIRType>();
    private generatedBlocks: Map<string, string[]> = new Map<string, string[]>();

    constructor(assembly: MIRAssembly, typegen: CPPTypeEmitter) {
        this.assembly = assembly;
        this.typegen = typegen;

        this.currentRType = typegen.noneType;
    }

    generateInit(trgt: MIRRegisterArgument, value: string): string {
        const ttype = this.getArgType(trgt);
        if (isInlinableType(ttype)) {
            if (ttype.trkey === "NSCore::Bool") {
                return `${this.varToCppName(trgt)} = ${value};`;
            }
            else {
                return `${this.varToCppName(trgt)} = ${value};`;
            }
        }
        else if (isUniqueEntityType(ttype)) {
            return `${this.varToCppName(trgt)} = ${value};`;
        }
        else {
            return `${this.varToCppName(trgt)} = ${value};`;
        }
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

    labelToCpp(label: string): string {
        return sanitizeForCpp(label);
    }

    varNameToCppName(name: string): string {
        return sanitizeForCpp(name);
    }

    varToCppName(varg: MIRRegisterArgument): string {
        return sanitizeForCpp(varg.nameID);
    }

    constNameToCppName(cname: string): string {
        return sanitizeForCpp(cname);
    }

    invokenameToCppName(invk: string): string {
        return sanitizeForCpp(invk);
    }

    boxIfNeeded(exp: string, from: MIRType, into: MIRType): string {
        if (isInlinableType(from) && !isInlinableType(into)) {
            const itype = getInlinableType(into);
            if (itype.trkey === "NSCore::Bool") {
                return `BSQ_BOX_VALUE_BOOL(${exp})`;
            }
            else {
                return `BSQ_BOX_VALUE_INT(${exp})`;
            }
        }
        else if (isUniqueEntityType(from) && !isUniqueEntityType(into)) {
            return `${exp}`;
        }
        else {
            return exp;
        }
    }

    unboxIfNeeded(exp: string, from: MIRType, into: MIRType): string {
        if (!isInlinableType(from) && isInlinableType(into)) {
            const itype = getInlinableType(into);
            if (itype.trkey === "NSCore::Bool") {
                return `BSQ_GET_VALUE_BOOL(${exp})`;
            }
            else {
                return `BSQ_GET_VALUE_INT(${exp})`;
            }
        }
        else if (!isUniqueEntityType(from) && isUniqueEntityType(into)) {
            return `BSQ_GET_VALUE_PTR(${exp}, ${sanitizeForCpp(into.trkey)})`;
        }
        else {
            return exp;
        }
    }

    coerce(exp: string, from: MIRType, into: MIRType): string {
        if (isInlinableType(from) !== isInlinableType(into)) {
            return isInlinableType(from) ? this.boxIfNeeded(exp, from, into) : this.unboxIfNeeded(exp, from, into);
        }
        else if (isUniqueEntityType(from) !== isUniqueEntityType(into)) {
            return isUniqueEntityType(from) ? this.boxIfNeeded(exp, from, into) : this.unboxIfNeeded(exp, from, into);
        }
        else {
            return exp;
        }
    }

    generateConstantExp(cval: MIRConstantArgument, into: MIRType | MIRTypeOption): string {
        const isinlineable = isInlinableType(into);

        if (cval instanceof MIRConstantNone) {
            return "BSQ_VALUE_NONE";
        }
        else if (cval instanceof MIRConstantTrue) {
            return isinlineable ? "true" : "BSQ_VALUE_TRUE";
        }
        else if (cval instanceof MIRConstantFalse) {
            return isinlineable ? "false" : "BSQ_VALUE_FALSE";
        }
        else if (cval instanceof MIRConstantInt) {
            if (isinlineable) {
                return cval.value;
            }
            else {
                if (cval.value === "0") {
                    return "BSQ_VALUE_0";
                }
                else if (cval.value === "1") {
                    return "BSQ_VALUE_POS_1";
                }
                else if (cval.value === "-1") {
                    return "BSQ_VALUE_NEG_1";
                }
                else {
                    return `BSQ_BOX_VALUE_INT(${cval.value})`;
                }
            }
        }
        else {
            assert(cval instanceof MIRConstantString);

            const sval = (cval as MIRConstantString).value;
            const sname = "str$" + this.allConstStrings.size;
            if (!this.allConstStrings.has(sval)) {
                this.allConstStrings.set(sval, sname);
            }

            return `(&Runtime::${sname})`;
        }
    }

    argToCpp(arg: MIRArgument, into: MIRType): string {
        if (arg instanceof MIRRegisterArgument) {
            return this.coerce(this.varToCppName(arg), this.getArgType(arg), into);
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

    generateMIRInvokeFixedFunction(ivop: MIRInvokeFixedFunction): string {
        let vals: string[] = [];
        const idecl = (this.assembly.invokeDecls.get(ivop.mkey) || this.assembly.primitiveInvokeDecls.get(ivop.mkey)) as MIRInvokeDecl;

        for (let i = 0; i < ivop.args.length; ++i) {
            vals.push(this.argToCpp(ivop.args[i], this.assembly.typeMap.get(idecl.params[i].type) as MIRType));
        }

        if (!isInlinableType(this.assembly.typeMap.get(ivop.resultType) as MIRType)) {
            vals.push(`$scope$.getCallerSlot<${this.scopectr++}>()`);
        }

        return `${this.invokenameToCppName(ivop.mkey)}(${vals.join(", ")})`;
    }

    generateFastEquals(op: string, lhs: MIRArgument, rhs: MIRArgument): string {
        const lhvtype = this.getArgType(lhs);
        const rhvtype = this.getArgType(rhs);

        if (lhvtype.trkey === "NSCore::Bool" && rhvtype.trkey === "NSCore::Bool") {
            return `${this.argToCpp(lhs, this.typegen.boolType)} ${op} ${this.argToCpp(rhs, this.typegen.boolType)}`;
        }
        else {
            return `${this.argToCpp(lhs, this.typegen.intType)} ${op} ${this.argToCpp(rhs, this.typegen.intType)}`;
        }
    }

    generateFastCompare(op: string, lhs: MIRArgument, rhs: MIRArgument): string {
        return `${this.argToCpp(lhs, this.typegen.intType)} ${op} ${this.argToCpp(rhs, this.typegen.intType)}`;
    }

    generateStmt(op: MIROp, supportcalls: string[]): string | undefined {
        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const lcv = (op as MIRLoadConst);
                return this.generateInit(lcv.trgt, this.generateConstantExp(lcv.src, this.getArgType(lcv.trgt)));
            }
            case MIROpTag.MIRLoadConstTypedString:  {
                return NOT_IMPLEMENTED<string>("MIRLoadConstTypedString");
            }
            case MIROpTag.MIRAccessConstantValue: {
                return NOT_IMPLEMENTED<string>("MIRAccessConstantValue");
            }
            case MIROpTag.MIRLoadFieldDefaultValue: {
                return NOT_IMPLEMENTED<string>("MIRLoadFieldDefaultValue");
            }
            case MIROpTag.MIRAccessArgVariable: {
                const lav = (op as MIRAccessArgVariable);
                return this.generateInit(lav.trgt, this.argToCpp(lav.name, this.getArgType(lav.trgt)));
            }
            case MIROpTag.MIRAccessLocalVariable: {
                const llv = (op as MIRAccessLocalVariable);
                return this.generateInit(llv.trgt, this.argToCpp(llv.name, this.getArgType(llv.trgt)));
            }
            case MIROpTag.MIRConstructorPrimary: {
                return NOT_IMPLEMENTED<string>("MIRConstructorPrimary");
            }
            case MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
                return NOT_IMPLEMENTED<string>("MIRConstructorPrimaryCollectionEmpty");
            }
            case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                return NOT_IMPLEMENTED<string>("MIRConstructorPrimaryCollectionSingletons");
            }
            case MIROpTag.MIRConstructorPrimaryCollectionCopies: {
                return NOT_IMPLEMENTED<string>("MIRConstructorPrimaryCollectionCopies");
            }
            case MIROpTag.MIRConstructorPrimaryCollectionMixed: {
                return NOT_IMPLEMENTED<string>("MIRConstructorPrimaryCollectionMixed");
            }
            case MIROpTag.MIRConstructorTuple: {
                return NOT_IMPLEMENTED<string>("MIRConstructorTuple");
            }
            case MIROpTag.MIRConstructorRecord: {
                return NOT_IMPLEMENTED<string>("MIRConstructorRecord");
            }
            case MIROpTag.MIRAccessFromIndex: {
                return NOT_IMPLEMENTED<string>("MIRAccessFromIndex");
            }
            case MIROpTag.MIRProjectFromIndecies: {
                return NOT_IMPLEMENTED<string>("MIRProjectFromIndecies");
            }
            case MIROpTag.MIRAccessFromProperty: {
                return NOT_IMPLEMENTED<string>("MIRAccessFromProperty");
            }
            case MIROpTag.MIRProjectFromProperties: {
                return NOT_IMPLEMENTED<string>("MIRProjectFromProperties");
            }
            case MIROpTag.MIRAccessFromField: {
                return NOT_IMPLEMENTED<string>("MIRAccessFromField");
            }
            case MIROpTag.MIRProjectFromFields: {
                return NOT_IMPLEMENTED<string>("MIRProjectFromFields");
            }
            case MIROpTag.MIRProjectFromTypeTuple: {
                return NOT_IMPLEMENTED<string>("MIRProjectFromTypeTuple");
            }
            case MIROpTag.MIRProjectFromTypeRecord: {
                return NOT_IMPLEMENTED<string>("MIRProjectFromTypeRecord");
            }
            case MIROpTag.MIRProjectFromTypeConcept: {
                return NOT_IMPLEMENTED<string>("MIRProjectFromTypeConcept");
            }
            case MIROpTag.MIRModifyWithIndecies: {
                return NOT_IMPLEMENTED<string>("MIRModifyWithIndecies");
            }
            case MIROpTag.MIRModifyWithProperties: {
                return NOT_IMPLEMENTED<string>("MIRModifyWithProperties");
            }
            case MIROpTag.MIRModifyWithFields: {
                return NOT_IMPLEMENTED<string>("MIRModifyWithFields");
            }
            case MIROpTag.MIRStructuredExtendTuple: {
                return NOT_IMPLEMENTED<string>("MIRStructuredExtendTuple");
            }
            case MIROpTag.MIRStructuredExtendRecord: {
                return NOT_IMPLEMENTED<string>("MIRStructuredExtendRecord");
            }
            case MIROpTag.MIRStructuredExtendObject: {
                return NOT_IMPLEMENTED<string>("MIRStructuredExtendObject");
            }
            case MIROpTag.MIRInvokeFixedFunction: {
                const invk = op as MIRInvokeFixedFunction;
                return this.generateInit(invk.trgt, this.generateMIRInvokeFixedFunction(invk));
            }
            case MIROpTag.MIRInvokeVirtualTarget: {
                return NOT_IMPLEMENTED<string>("MIRInvokeVirtualTarget");
            }
            case MIROpTag.MIRPrefixOp: {
                const pfx = op as MIRPrefixOp;
                if (pfx.op === "!") {
                    const tval = this.generateTruthyConvert(pfx.arg);
                    return this.generateInit(pfx.trgt, `!${tval}`);
                }
                else {
                    if (pfx.op === "-") {
                        return this.generateInit(pfx.trgt, `-${this.argToCpp(pfx.arg, this.typegen.intType)}`);
                    }
                    else {
                        return this.generateInit(pfx.trgt, `${this.argToCpp(pfx.arg, this.typegen.intType)}`);
                    }
                }
            }
            case MIROpTag.MIRBinOp: {
                const bop = op as MIRBinOp;
                if (bop.op === "+") {
                    return `BSQ_OP_ADD(${this.varToCppName(bop.trgt)}, ${this.argToCpp(bop.lhs, this.typegen.intType)}, ${this.argToCpp(bop.rhs, this.typegen.intType)}, "${filenameClean(this.currentFile)}", ${op.sinfo.line})`;
                }
                else if (bop.op === "-") {
                    return `BSQ_OP_SUB(${this.varToCppName(bop.trgt)}, ${this.argToCpp(bop.lhs, this.typegen.intType)}, ${this.argToCpp(bop.rhs, this.typegen.intType)}, "${filenameClean(this.currentFile)}", ${op.sinfo.line})`;
                }
                else if (bop.op === "-") {
                    return `BSQ_OP_MULT(${this.varToCppName(bop.trgt)}, ${this.argToCpp(bop.lhs, this.typegen.intType)}, ${this.argToCpp(bop.rhs, this.typegen.intType)}, "${filenameClean(this.currentFile)}", ${op.sinfo.line})`;
                }
                else if (bop.op === "-") {
                    return `BSQ_OP_DIV(${this.varToCppName(bop.trgt)}, ${this.argToCpp(bop.lhs, this.typegen.intType)}, ${this.argToCpp(bop.rhs, this.typegen.intType)}, "${filenameClean(this.currentFile)}", ${op.sinfo.line})`;
                }
                else {
                    return `BSQ_OP_MOD(${this.varToCppName(bop.trgt)}, ${this.argToCpp(bop.lhs, this.typegen.intType)}, ${this.argToCpp(bop.rhs, this.typegen.intType)}, "${filenameClean(this.currentFile)}", ${op.sinfo.line})`;
                }
            }
            case MIROpTag.MIRBinEq: {
                const beq = op as MIRBinEq;

                const lhvtype = this.getArgType(beq.lhs);
                const rhvtype = this.getArgType(beq.rhs);
                if (isInlinableType(lhvtype) && isInlinableType(rhvtype)) {
                    return this.generateInit(beq.trgt, this.generateFastEquals(beq.op, beq.lhs, beq.rhs));
                }
                else {
                    const larg = this.argToCpp(beq.lhs, this.typegen.anyType);
                    const rarg = this.argToCpp(beq.rhs, this.typegen.anyType);

                    return this.generateInit(beq.trgt, `${beq.op === "!=" ? "!" : ""}Runtime::equality_op(${larg}, ${rarg})`);
                }
            }
            case MIROpTag.MIRBinCmp: {
                const bcmp = op as MIRBinCmp;

                const lhvtype = this.getArgType(bcmp.lhs);
                const rhvtype = this.getArgType(bcmp.rhs);

                if (isInlinableType(lhvtype) && isInlinableType(rhvtype)) {
                    return this.generateInit(bcmp.trgt, this.generateFastCompare(bcmp.op, bcmp.lhs, bcmp.rhs));
                }
                else {
                    const larg = this.argToCpp(bcmp.lhs, this.typegen.anyType);
                    const rarg = this.argToCpp(bcmp.rhs, this.typegen.anyType);

                    if (bcmp.op === "<") {
                        return this.generateInit(bcmp.trgt, `Runtime::compare_op(${larg}, ${rarg})`);
                    }
                    else if (bcmp.op === ">") {
                        return this.generateInit(bcmp.trgt, `Runtime::compare_op(${rarg}, ${larg})`);
                    }
                    else if (bcmp.op === "<=") {
                        return this.generateInit(bcmp.trgt, `Runtime::compare_op(${larg}, ${rarg}) || Runtime::equality_op(${larg}, ${rarg})`);
                    }
                    else {
                        return this.generateInit(bcmp.trgt, `Runtime::compare_op(${rarg}, ${larg}) || Runtime::equality_op(${larg}, ${rarg})`);
                    }
                }
            }
            case MIROpTag.MIRIsTypeOfNone: {
                const ton = op as MIRIsTypeOfNone;

                if (isInlinableType(this.getArgType(ton.arg))) {
                    return "false";
                }
                else {
                    return this.generateInit(ton.trgt, `BSQ_IS_VALUE_NONE(${this.varToCppName(ton.arg)})`);
                }
            }
            case MIROpTag.MIRIsTypeOfSome: {
                const tos = op as MIRIsTypeOfSome;

                if (isInlinableType(this.getArgType(tos.arg))) {
                    return "true";
                }
                else {
                    return this.generateInit(tos.trgt, `BSQ_IS_VALUE_NONNONE(${this.varToCppName(tos.arg)})`);
                }
           }
            case MIROpTag.MIRIsTypeOf: {
                return NOT_IMPLEMENTED<string>("MIRIsTypeOf");
            }
            case MIROpTag.MIRRegAssign: {
                const regop = op as MIRRegAssign;
                return this.generateInit(regop.trgt, this.argToCpp(regop.src, this.getArgType(regop.trgt)));
            }
            case MIROpTag.MIRTruthyConvert: {
                const tcop = op as MIRTruthyConvert;
                return this.generateInit(tcop.trgt, this.generateTruthyConvert(tcop.src));
            }
            case MIROpTag.MIRLogicStore: {
                const llop = op as MIRLogicStore;
                return this.generateInit(llop.trgt, `(${this.argToCpp(llop.lhs, this.typegen.boolType)} ${llop.op} ${this.argToCpp(llop.rhs, this.typegen.boolType)})`);
            }
            case MIROpTag.MIRVarStore: {
                const vsop = op as MIRVarStore;
                return this.generateInit(vsop.name, this.argToCpp(vsop.src, this.getArgType(vsop.name)));
            }
            case MIROpTag.MIRReturnAssign: {
                const raop = op as MIRReturnAssign;
                return this.generateInit(raop.name, this.argToCpp(raop.src, this.getArgType(raop.name)));
            }
            case MIROpTag.MIRAbort: {
                const aop = (op as MIRAbort);
                return `BSQ_ABORT("${aop.info}", "[TODO: filename]", ${aop.sinfo.line});`;
            }
            case MIROpTag.MIRDebug: {
                //debug is a nop in AOT release mode but we allow it for our debugging purposes
                const dbgop = op as MIRDebug;
                if (dbgop.value === undefined) {
                    return "assert(false);";
                }
                else {
                    return `printf(Runtime::diagnostic_format(${this.argToCpp(dbgop.value, this.typegen.anyType)}).c_str()); printf("\\n");`;
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
                const argtype = this.getArgType(njop.arg);
                if (isInlinableType(argtype)) {
                    return `goto ${this.labelToCpp(njop.someblock)};`;
                }
                else {
                    return `if(BSQ_IS_VALUE_NONE(${this.argToCpp(njop.arg, this.typegen.anyType)})) {goto ${this.labelToCpp(njop.noneblock)};} else {goto ${njop.someblock};}`;
                }
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

    generateBlock(block: MIRBasicBlock, supportcalls: string[]) {
        let gblock: string[] = [];

        let blocki = 0;
        while (blocki < block.ops.length - 1 && block.ops[blocki] instanceof MIRPhi) {
            const phiop = block.ops[blocki] as MIRPhi;
            phiop.src.forEach((src, fblock) => {
                const assign = this.generateInit(phiop.trgt, this.argToCpp(src, this.getArgType(phiop.trgt)));
                const inblock = this.generatedBlocks.get(fblock) as string[];

                //last entry is the jump so put before that but after all other statements
                const jmp = inblock[inblock.length - 1];
                inblock[inblock.length - 1] = assign;
                inblock.push(jmp);
            });

            ++blocki;
        }

        while (blocki < block.ops.length) {
            const gop = this.generateStmt(block.ops[blocki], supportcalls);
            if (gop !== undefined) {
                gblock.push(gop);
            }

            ++blocki;
        }

        if (block.label === "exit") {
            if (!isInlinableType(this.currentRType)) {
                if (!this.assembly.subtypeOf(this.typegen.boolType, this.currentRType) && !this.assembly.subtypeOf(this.typegen.intType, this.currentRType)) {
                    if (this.assembly.subtypeOf(this.typegen.noneType, this.currentRType)) {
                        gblock.push("RefCountScopeCallMgr::processCallRefNoneable($callerslot$, _return_);");
                    }
                    else {
                        gblock.push("RefCountScopeCallMgr::processCallReturnFast($callerslot$, _return_);");
                    }
                }
                else {
                    gblock.push("RefCountScopeCallMgr::processCallRefAny($callerslot$, _return_);");
                }
            }

            gblock.push("return _return_;");
        }

        this.generatedBlocks.set(block.label, gblock);
    }

    generateCPPInvoke(idecl: MIRInvokeDecl): { fwddecl: string, fulldecl: string, supportcalls: string[] } {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.assembly.typeMap.get(idecl.resultType) as MIRType;
        this.scopectr = 0;

        const args = idecl.params.map((arg) => `${this.typegen.typeToCPPType(this.assembly.typeMap.get(arg.type) as MIRType)} ${this.varNameToCppName(arg.name)}`);
        const restype = this.typegen.typeToCPPType(this.assembly.typeMap.get(idecl.resultType) as MIRType);

        if (!isInlinableType(this.assembly.typeMap.get(idecl.resultType) as MIRType)) {
            args.push("RefCountBase** $callerslot$");
        }
        const decl = `${restype} ${this.invokenameToCppName(idecl.key)}(${args.join(", ")})`;

        if (idecl instanceof MIRInvokeBodyDecl) {
            this.vtypes = new Map<string, MIRType>();
            (idecl.body.vtypes as Map<string, string>).forEach((tkey, name) => {
                this.vtypes.set(name, this.assembly.typeMap.get(tkey) as MIRType);
            });

            this.generatedBlocks = new Map<string, string[]>();
            let supportcalls: string[] = [];

            const blocks = topologicalOrder((idecl as MIRInvokeBodyDecl).body.body);
            for (let i = 0; i < blocks.length; ++i) {
                this.generateBlock(blocks[i], supportcalls);
            }

            const refscope = this.scopectr !== 0 ? `RefCountScope<${this.scopectr}> $scope$;` : ";";

            let vdecls = new Map<string, string[]>();
            (idecl.body.vtypes as Map<string, string>).forEach((tkey, name) => {
                if (idecl.params.findIndex((p) => p.name === name) === -1) {
                    const declt = this.typegen.typeToCPPType(this.assembly.typeMap.get(tkey) as MIRType);
                    if (!vdecls.has(declt)) {
                        vdecls.set(declt, [] as string[]);
                    }

                    (vdecls.get(declt) as string[]).push(sanitizeForCpp(name));
                }
            });
            let vdeclscpp: string[] = [];
            if (vdecls.has("bool")) {
                vdeclscpp.push(`bool ${(vdecls.get("bool") as string[]).join(", ")};`);
            }
            if (vdecls.has("int64_t")) {
                vdeclscpp.push(`int64_t ${(vdecls.get("int64_t") as string[]).join(", ")};`);
            }
            [...vdecls].sort((a, b) => a[0].localeCompare(b[0])).forEach((kv) => {
                if (kv[0] !== "bool" && kv[0] !== "int64_t") {
                    vdeclscpp.push(kv[1].map((vname) => `${kv[0]} ${vname}`).join("; ") + ";");
                }
            });

            if (idecl.preconditions.length === 0 && idecl.postconditions.length === 0) {
                const blockstrs = [...this.generatedBlocks].map((blck) => {
                    const lbl = `${this.labelToCpp(blck[0])}:\n`;
                    const stmts = blck[1].map((stmt) => "    " + stmt).join("\n");
                    return lbl + stmts;
                });

                const scopestrs = [refscope, ...vdeclscpp].join("\n");

                return { fwddecl: decl + ";", fulldecl: `${decl}\n{\n${scopestrs}\n\n${blockstrs.join("\n\n")}\n}\n`, supportcalls: supportcalls };
            }
            else {
                return NOT_IMPLEMENTED<{ fwddecl: string, fulldecl: string, supportcalls: string[] }>("generateInvoke -- Pre/Post");
            }
        }
        else {
            assert(idecl instanceof MIRInvokePrimitiveDecl);

            return NOT_IMPLEMENTED<{ fwddecl: string, fulldecl: string, supportcalls: string[] }>("generateInvoke -- MIRInvokePrimitiveDecl");
        }
    }
}

export {
    CPPBodyEmitter
};
