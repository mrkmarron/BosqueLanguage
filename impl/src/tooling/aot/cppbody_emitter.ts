//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIRInvokeDecl, MIRInvokeBodyDecl, MIRInvokePrimitiveDecl, MIRConstantDecl, MIRFieldDecl, MIREntityTypeDecl, MIRFunctionParameter, MIREntityType, MIRTupleType, MIRRecordType, MIRConceptType, MIREphemeralListType, MIRPCode, MIRRegex } from "../../compiler/mir_assembly";
import { CPPTypeEmitter } from "./cpptype_emitter";
import { MIRArgument, MIRRegisterArgument, MIRConstantNone, MIRConstantFalse, MIRConstantTrue, MIRConstantInt, MIRConstantArgument, MIRConstantString, MIROp, MIROpTag, MIRLoadConst, MIRAccessArgVariable, MIRAccessLocalVariable, MIRInvokeFixedFunction, MIRPrefixOp, MIRBinOp, MIRBinEq, MIRBinCmp, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRRegAssign, MIRTruthyConvert, MIRVarStore, MIRReturnAssign, MIRDebug, MIRJump, MIRJumpCond, MIRJumpNone, MIRAbort, MIRBasicBlock, MIRPhi, MIRConstructorTuple, MIRConstructorRecord, MIRAccessFromIndex, MIRAccessFromProperty, MIRInvokeKey, MIRAccessConstantValue, MIRLoadFieldDefaultValue, MIRBody, MIRConstructorPrimary, MIRAccessFromField, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionSingletons, MIRIsTypeOf, MIRProjectFromIndecies, MIRModifyWithIndecies, MIRStructuredExtendTuple, MIRProjectFromProperties, MIRModifyWithProperties, MIRStructuredExtendRecord, MIRLoadConstTypedString, MIRConstructorEphemeralValueList, MIRProjectFromFields, MIRModifyWithFields, MIRStructuredExtendObject, MIRLoadConstSafeString, MIRInvokeInvariantCheckDirect, MIRLoadFromEpehmeralList, MIRConstantBigInt, MIRConstantFloat64, MIRFieldKey, MIRResolvedTypeKey, MIRPackSlice, MIRPackExtend, MIRNominalTypeKey, MIRBinLess, MIRConstantRegex } from "../../compiler/mir_ops";
import { topologicalOrder } from "../../compiler/mir_info";
import { StructRepr, RefRepr, ValueRepr, KeyValueRepr, NoneRepr, UnionRepr, StorageByteAlignment, TRRepr } from "./type_repr";
import { compileRegexCppMatch } from "./cpp_regex";
import { CPPFrame } from "./cpp_frame";

import * as assert from "assert";
import { CoerceKind, coerce, isDirectReturnValue, getRequiredCoerce, coerseAssignCPPValue, coerceInline } from "./cpp_loadstore";

function NOT_IMPLEMENTED<T>(msg: string): T {
    throw new Error(`Not Implemented: ${msg}`);
}

function filenameClean(file: string): string {
    return file.replace(/[\\]/g, "/");
}

const CPP_EXECUTION_POLICY = "std::execution::par_unseq";

class CPPBodyEmitter {
    readonly assembly: MIRAssembly;
    readonly typegen: CPPTypeEmitter;
    
    readonly allPropertyNames: Set<string> = new Set<string>();
    readonly allConstStrings: Map<string, string> = new Map<string, string>();
    readonly allConstRegexes: Map<string, string> = new Map<string, string>();
    readonly allConstBigInts: Map<string, string> = new Map<string, string>();

    private cppframe: CPPFrame;
    private currentFile: string = "[No File]";
    private currentRType: MIRType;

    private vtypes: Map<string, MIRType> = new Map<string, MIRType>();
    private generatedBlocks: Map<string, string[]> = new Map<string, string[]>();

    private subtypeOrderCtr = 0;
    subtypeFMap: Map<string, {order: number, decl: string}> = new Map<string, {order: number, decl: string}>();
    checkedConcepts: Set<MIRResolvedTypeKey> = new Set<MIRResolvedTypeKey>();

    vfieldLookups: { infertype: MIRType, fdecl: MIRFieldDecl, lname: string }[] = [];
    vfieldProjects: { infertype: MIRType, fprojs: MIRFieldDecl[], resultAccessType: MIRType, uname: string }[] = [];
    vfieldUpdates: { infertype: MIRType, fupds: [MIRFieldDecl, MIRArgument][], resultAccessType: MIRType, uname: string }[] = [];
    vobjmerges: { infertype: MIRType, merge: MIRArgument, infermergetype: MIRType, fieldResolves: [string, MIRFieldDecl][], resultAccessType: MIRType, mname: string }[] = [];

    constructor(assembly: MIRAssembly, typegen: CPPTypeEmitter) {
        this.assembly = assembly;
        this.typegen = typegen;
        
        this.currentRType = typegen.noneType;
        this.cppframe = new CPPFrame();
    }

    labelToCpp(label: string): string {
        return label;
    }

    varNameToCppName(name: string): string {
        if (name === "this") {
            return this.typegen.mangleStringForCpp("$this");
        }
        else if (name === "$$return") {
            return "$$return";
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
            else if (arg instanceof MIRConstantString) {
                return this.typegen.stringType;
            }
            else {
                return this.typegen.regexType;
            }
        }
    }

    ensureLocationForTrgt(loc: MIRRegisterArgument) {
        this.cppframe.ensureLocationForVariable(this.varToCppName(loc), this.typegen.getCPPReprFor(this.getArgType(loc)));
    }

    getConstantSrc(cval: MIRConstantArgument): string {
        if (cval instanceof MIRConstantNone) {
            return "BSQ_NONE";
        }
        else if (cval instanceof MIRConstantTrue) {
            return "BSQTRUE";
        }
        else if (cval instanceof MIRConstantFalse) {
            return "BSQFALSE";
        }
        else if (cval instanceof MIRConstantInt) {
            return cval.value;
        }
        else if (cval instanceof MIRConstantBigInt) {
            const sname = "BIGINT__" + this.allConstBigInts.size;
            if (!this.allConstBigInts.has(cval.value)) {
                this.allConstBigInts.set(cval.value, sname);
            }

            return `Runtime::${this.allConstBigInts.get(cval.value) as string}`;
        }
        else if (cval instanceof MIRConstantFloat64) {
            return cval.digits();
        }
        else if (cval instanceof MIRConstantString) {
            assert(cval instanceof MIRConstantString);

            const sval = (cval as MIRConstantString).value;
            const sname = "STR__" + this.allConstStrings.size;
            if (!this.allConstStrings.has(sval)) {
                this.allConstStrings.set(sval, sname);
            }

            return `Runtime::${this.allConstStrings.get(sval) as string}`;
        }
        else {
            assert(cval instanceof MIRConstantRegex);

            const rval = (cval as MIRConstantRegex).value;
            const rname = "REGEX__" + this.allConstRegexes.size;
            if (!this.allConstRegexes.has(rval)) {
                this.allConstRegexes.set(rval, rname);
            }

            return `Runtime::${this.allConstRegexes.get(rval) as string}`;
        }
    }

    generateArgSrc(arg: MIRArgument): string {
        if (arg instanceof MIRRegisterArgument) {
            return this.cppframe.getExpressionForName(this.varToCppName(arg));
        }
        else {
            return this.getConstantSrc(arg as MIRConstantArgument);
        }
    }

    generateArgStore(arg: MIRRegisterArgument): string {
        return this.cppframe.getExpressionForName(this.varToCppName(arg));
    }

    coerceArgsPlus(xsize: number, ...args: [MIRArgument, MIRType][]): [string[], string[]] {
        let nargs: string[] = [];
        let ops: string[] = [];
    
        let rsize = 0;
        for(let i = 0; i < args.length; ++i) {
            const [arg, into] = args[i];
            const argrepr = this.typegen.getCPPReprFor(this.getArgType(arg));
            const intorepr = this.typegen.getCPPReprFor(into);
    
            const cci = getRequiredCoerce(argrepr, intorepr);
            rsize += cci.alloc;

            const argc = this.generateArgSrc(arg);
            let [nval, nops] = coerce(this.cppframe, argc, argrepr, intorepr);

            nargs.push(nval);
            ops = [...ops, ...nops];
        }

        if(rsize !== 0) {
            ops = [`Allocator::GlobalAllocator.ensureSpace<${rsize + xsize}>();`, ...ops];
        }

        return [nargs, ops];
    }

    coerceArgs(...args: [MIRArgument, MIRType][]): [string[], string[]] {
        return this.coerceArgsPlus(0, ...args);
    }

    coerceArgsInlinePlus(xsize: number, ...args: [MIRArgument, MIRType][]): [string[], string[]] {
        let nargs: string[] = [];
        let ops: string[] = [];
    
        let rsize = 0;
        for(let i = 0; i < args.length; ++i) {
            const [arg, into] = args[i];
            const argrepr = this.typegen.getCPPReprFor(this.getArgType(arg));
            const intorepr = this.typegen.getCPPReprFor(into);
    
            const cci = getRequiredCoerce(argrepr, intorepr);
            rsize += cci.alloc;

            const argc = this.generateArgSrc(arg);
            let [nval, nops] = coerceInline(this.cppframe, argc, argrepr, intorepr);

            nargs.push(nval);
            ops = [...ops, ...nops];
        }

        if(rsize !== 0) {
            ops = [`Allocator::GlobalAllocator.ensureSpace<${rsize + xsize}>();`, ...ops];
        }

        return [nargs, ops];
    }

    coerceArgsInline(...args: [MIRArgument, MIRType][]): [string[], string[]] {
        return this.coerceArgsInlinePlus(0, ...args);
    }

    coerceAccessPlus(xsize: number, ...args: [string, MIRType, MIRType][]): [string[], string[]] {
        let nargs: string[] = [];
        let ops: string[] = [];
    
        let rsize = 0;
        for(let i = 0; i < args.length; ++i) {
            const [arg, from, into] = args[i];
            const argrepr = this.typegen.getCPPReprFor(from);
            const intorepr = this.typegen.getCPPReprFor(into);
    
            const cci = getRequiredCoerce(argrepr, intorepr);
            rsize += cci.alloc;

            let [nval, nops] = coerce(this.cppframe, arg, argrepr, intorepr);

            nargs.push(nval);
            ops = [...ops, ...nops];
        }

        if(rsize !== 0) {
            ops = [`Allocator::GlobalAllocator.ensureSpace<${rsize + xsize}>();`, ...ops];
        }

        return [nargs, ops];
    }

    coerceAccess(...args: [string, MIRType, MIRType][]): [string[], string[]] {
        return this.coerceAccessPlus(0, ...args);
    }

    coerceAccessInlinePlus(xsize: number, ...args: [string, MIRType, MIRType][]): [string[], string[]] {
        let nargs: string[] = [];
        let ops: string[] = [];
    
        let rsize = 0;
        for(let i = 0; i < args.length; ++i) {
            const [arg, from, into] = args[i];
            const argrepr = this.typegen.getCPPReprFor(from);
            const intorepr = this.typegen.getCPPReprFor(into);
    
            const cci = getRequiredCoerce(argrepr, intorepr);
            rsize += cci.alloc;

            let [nval, nops] = coerceInline(this.cppframe, arg, argrepr, intorepr);

            nargs.push(nval);
            ops = [...ops, ...nops];
        }

        if(rsize !== 0) {
            ops = [`Allocator::GlobalAllocator.ensureSpace<${rsize + xsize}>();`, ...ops];
        }

        return [nargs, ops];
    }

    coerceAccessInline(...args: [string, MIRType, MIRType][]): [string[], string[]] {
        return this.coerceAccessInlinePlus(0, ...args);
    }

    coerceResult(result: string, oftype: MIRType, intoname: string, intotype: MIRType): string[] {
        const resrepr = this.typegen.getCPPReprFor(oftype);
        const intorepr = this.typegen.getCPPReprFor(intotype);

        const intoloc = this.cppframe.getExpressionForName(intoname);

        const cci = getRequiredCoerce(resrepr, intorepr);
        if (cci.alloc === 0) {
            return coerseAssignCPPValue(this.cppframe, result, intoloc, resrepr, intorepr);
        }
        else {
            let ops: string[] = [];

            ops.push(`Allocator::GlobalAllocator.ensureSpace<${cci.alloc}>();`);
            let caops = coerseAssignCPPValue(this.cppframe, result, intoloc, resrepr, intorepr);

            return [...ops, ...caops];
        }
    }

    isConstInvoke(inv: MIRInvokeDecl): boolean {
        if (!(inv instanceof MIRInvokeBodyDecl)) {
            return false;
        }

        const op0 = (inv.body.body.get("entry") as MIRBasicBlock).ops[0];
        return op0 instanceof MIRReturnAssign && op0.src instanceof MIRConstantArgument; 
    }

    getConstantInvokeValue(inv: MIRInvokeDecl): MIRConstantArgument {
        const op0 = ((inv as MIRInvokeBodyDecl).body.body.get("entry") as MIRBasicBlock).ops[0];
        return (op0 as MIRReturnAssign).src as MIRConstantArgument;
    }

    generateInvokeInto(intov: string, intot: MIRType, inv: MIRInvokeDecl, args: MIRArgument[]): string[] {
        const rrepr = this.typegen.getCPPReprFor(this.typegen.getMIRType(inv.resultType));
        const intorepr = this.typegen.getCPPReprFor(intot);

        if (this.isConstInvoke(inv)) {
            const cres = this.getConstantInvokeValue(inv);
            return this.coerceResult(this.getConstantSrc(cres), this.getArgType(cres), intov, intot);
        }
        else {
            let argpairs: [MIRArgument, MIRType][] = [];
            for (let i = 0; i < args.length; ++i) {
                argpairs.push([args[i], this.typegen.getMIRType(inv.params[i].type)]);
            }

            const [cargs, ops] = this.coerceArgs(...argpairs);
            if (isDirectReturnValue(rrepr)) {
                const invc = `${this.invokenameToCPP(inv.key)}(${cargs.join(", ")})`;
                const rvops = this.coerceResult(invc, this.typegen.getMIRType(inv.resultType), intov, intot);

                return [...ops, ...rvops];
            }
            else {
                const cci = getRequiredCoerce(rrepr, intorepr);
                if (cci.kind === CoerceKind.None) {
                    cargs.push(intov);
                    const invc = `${this.invokenameToCPP(inv.key)}(${cargs.join(", ")});`;

                    return [...ops, invc];
                }
                else {
                    const tmploc = this.cppframe.generateFreshName();
                    this.cppframe.ensureLocationForVariable(tmploc, rrepr);

                    cargs.push(tmploc);
                    const invc = `${this.invokenameToCPP(inv.key)}(${cargs.join(", ")});`;

                    const rvops = this.coerceResult(tmploc, this.typegen.getMIRType(inv.resultType), intov, intot);

                    return [...ops, invc, ...rvops];
                }
            }
        }
    }

    generateIndexExpression(arg: MIRArgument, idx: number): string {
        const tuptype = this.getArgType(arg);
        const hasidx = this.typegen.tupleHasIndex(tuptype, idx);
    
        if(hasidx === "no") {
            return "BSQ_VALUE_NONE";
        }
        else {
            const trepr = this.typegen.getCPPReprFor(tuptype);
            if(trepr instanceof TRRepr) {
                return `${this.cppframe.getExpressionForName(this.varToCppName(arg))}.atFixed<${idx}>()`;
            }
            else if (trepr instanceof UnionRepr) {
                return `(UnionValue::extractPointerToContent<BSQTupleDynamic>(${this.cppframe.getExpressionForName(this.varToCppName(arg))})->atFixed<${idx}>()`;
            }
            else {
                return `((BSQTupleDynamic*)${this.cppframe.getExpressionForName(this.varToCppName(arg))})->atFixed<${idx}>()`;
            }
        }
    }

    generatePropertyExpression(arg: MIRArgument, property: string): string {
        const rectype = this.getArgType(arg);
        const hasproperty = this.typegen.recordHasField(rectype, property);
    
        if(hasproperty === "no") {
            return "BSQ_VALUE_NONE";
        }
        else {
            const rrepr = this.typegen.getCPPReprFor(rectype);
            if(rrepr instanceof TRRepr) {
                return `${this.cppframe.getExpressionForName(this.varToCppName(arg))}.atFixed<MIRPropertyEnum::${property}>()`;
            }
            else if (rrepr instanceof UnionRepr) {
                return `(UnionValue::extractPointerToContent<BSQRecordDynamic>(${this.cppframe.getExpressionForName(this.varToCppName(arg))})->atFixed<${property}>()`;
            }
            else {
                return `((BSQTupleDynamic*)${this.cppframe.getExpressionForName(this.varToCppName(arg))})->atFixed<${property}>()`;
            }
        }
    }

    generateFieldExpressionKnown(arg: MIRArgument, infertype: MIRType, field: MIRFieldKey): string {
        const nrepr = this.typegen.getCPPReprFor(this.getArgType(arg));
        const irepr = this.typegen.getCPPReprFor(infertype)

        if (nrepr instanceof StructRepr) {
            return `${this.cppframe.getExpressionForName(this.varToCppName(arg))}.${this.typegen.mangleStringForCpp(field)}`;
        } 
        else if (nrepr instanceof RefRepr) {
            return `${this.cppframe.getExpressionForName(this.varToCppName(arg))}->${this.typegen.mangleStringForCpp(field)}`;
        }
        else if (nrepr instanceof UnionRepr) {
            if(irepr instanceof StructRepr) {
                return `(UnionValue::extractPointerToContent<${(irepr.storagetype)}>(${this.cppframe.getExpressionForName(this.varToCppName(arg))})->${this.typegen.mangleStringForCpp(field)}`;
            }
            else {
                return `(*(UnionValue::extractPointerToContent<${(irepr.storagetype)}>(${this.cppframe.getExpressionForName(this.varToCppName(arg))}))->${this.typegen.mangleStringForCpp(field)}`;
            }
        }
        else {
            return `((${(irepr.storagetype)})${this.cppframe.getExpressionForName(this.varToCppName(arg))})->${this.typegen.mangleStringForCpp(field)}`;
        }
    }

    generateTruthyConvert(arg: MIRArgument): string {
        const argtype = this.getArgType(arg);

        if (this.assembly.subtypeOf(argtype, this.typegen.noneType)) {
            return "false";
        }
        else if (this.assembly.subtypeOf(argtype, this.typegen.boolType)) {
            return this.generateArgSrc(arg);
        }
        else {
            const arepr = this.typegen.getCPPReprFor(this.getArgType(arg));
            if(arepr instanceof UnionRepr) {
                return `UnionValue::extractFromUnionPrimitive<BSQBool>(${this.generateArgSrc(arg)})`
            }
            else {
                return `(${this.generateArgSrc(arg)} == BSQ_VALUE_TRUE)`;
            }
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
            const arepr = this.typegen.getCPPReprFor(argtype);

            if(arepr instanceof RefRepr) {
                return `(${this.generateArgSrc(arg)} == BSQ_NONE_VALUE)`;
            }
            else if(arepr instanceof UnionRepr) {
                return `${this.generateArgSrc(arg)}.umeta->nominaltype == MIRNominalTypeEnum_None)`;
            }
            else {
                return `(${this.generateArgSrc(arg)} == BSQ_NONE_VALUE)`;
            }
        }
    }

    generateLoadConstSafeString(op: MIRLoadConstSafeString): string {
        const sval = op.ivalue;
        const sname = "STR__" + this.allConstStrings.size;

        if (!this.allConstStrings.has(sval)) {
            this.allConstStrings.set(sval, sname);
        }

        this.ensureLocationForTrgt(op.trgt);
        return `${this.generateArgStore(op.trgt)} = Runtime::${this.allConstStrings.get(sval) as string};`;
    }

    generateLoadConstTypedString(op: MIRLoadConstTypedString): string[] {
        const sval = op.ivalue;
        const sname = "STR__" + this.allConstStrings.size;

        if (!this.allConstStrings.has(sval)) {
            this.allConstStrings.set(sval, sname);
        }
        const strval = `Runtime::${this.allConstStrings.get(sval) as string}`;

        let opstrs: string[] = [];
        if(op.pfunckey !== undefined) {
            const pfunc = (this.typegen.assembly.invokeDecls.get(op.pfunckey) || this.typegen.assembly.primitiveInvokeDecls.get(op.pfunckey)) as MIRInvokeDecl;
            const errtype = this.typegen.getMIRType(op.errtype as MIRResolvedTypeKey);

            const tmp = this.cppframe.generateFreshName("strofchk");
            this.cppframe.ensureLocationForVariable(tmp, this.typegen.getCPPReprFor(this.typegen.getMIRType(pfunc.resultType)));
            const ops = this.generateInvokeInto(tmp, this.typegen.getMIRType(pfunc.resultType), pfunc, [new MIRConstantString(op.ivalue)]);

            const tcexp = this.generateTypeCheck(tmp, this.typegen.getMIRType(pfunc.resultType), this.typegen.getMIRType(pfunc.resultType), errtype);
            opstrs = [...ops, `BSQ_ASSERT(!(${tcexp}), "Failed string validation");`];
        }

        this.ensureLocationForTrgt(op.trgt);
        opstrs.push(`${this.generateArgStore(op.trgt)} = ${strval};`);

        return opstrs;
    }

    generateAccessConstantValue(cp: MIRAccessConstantValue): string[] {
        const cdecl = this.assembly.constantDecls.get(cp.ckey) as MIRConstantDecl;
        const idecl = (this.assembly.primitiveInvokeDecls.get(cdecl.value) || this.assembly.invokeDecls.get(cdecl.value)) as MIRInvokeDecl;

        this.ensureLocationForTrgt(cp.trgt);
        return this.generateInvokeInto(this.generateArgStore(cp.trgt), this.typegen.getMIRType(cdecl.declaredType), idecl, []);
    }

    generateLoadFieldDefaultValue(ld: MIRLoadFieldDefaultValue): string[] {
        const fdecl = this.assembly.fieldDecls.get(ld.fkey) as MIRFieldDecl;
        const idecl = (this.assembly.primitiveInvokeDecls.get(fdecl.value as MIRInvokeKey) || this.assembly.invokeDecls.get(fdecl.value as MIRInvokeKey)) as MIRInvokeDecl;

        this.ensureLocationForTrgt(ld.trgt);
        return this.generateInvokeInto(this.generateArgStore(ld.trgt), this.typegen.getMIRType(fdecl.declaredType), idecl, []);
    }

    generateMIRInvokeInvariantCheckDirect(ivop: MIRInvokeInvariantCheckDirect): string {
        const fields = [...(this.typegen.assembly.entityDecls.get(ivop.tkey) as MIREntityTypeDecl).fields];
        const argpreps = fields.map((f) => `${this.generateArgSrc(ivop.rcvr)}->${this.typegen.mangleStringForCpp(f.fkey)}`);

        this.ensureLocationForTrgt(ivop.trgt);
        return `${this.generateArgStore(ivop.trgt)} = ${this.invokenameToCPP(ivop.ikey)}(${argpreps.join(", ")});`;
    }

    generateMIRConstructorPrimary(cp: MIRConstructorPrimary): string[] {
        const ctype = this.assembly.entityDecls.get(cp.tkey) as MIREntityTypeDecl;

        let argpairs: [MIRArgument, MIRType][] = [];
        for (let i = 0; i < cp.args.length; ++i) {
            argpairs.push([cp.args[i], this.typegen.getMIRType(ctype.fields[i].declaredType)]);
        }
        
        const cppcrepr = this.typegen.getCPPReprFor(this.typegen.getMIRType(cp.tkey));
        if (cppcrepr instanceof StructRepr) {
            const [cargs, ops] = this.coerceArgsInline(...argpairs);

            this.ensureLocationForTrgt(cp.trgt);
            return [...ops, `${this.generateArgStore(cp.trgt)} = {${cargs.join(", ")}};`];
        }
        else {
            const crepr = this.typegen.getCPPReprFor(this.typegen.getMIRType(cp.tkey));
            const [cargs, ops] = this.coerceArgsInlinePlus(crepr.alignedSize + StorageByteAlignment, ...argpairs);

            this.ensureLocationForTrgt(cp.trgt);
            const alloc = `${this.generateArgStore(cp.trgt)} = Allocator::GlobalAllocator.allocateSafe<${cppcrepr.basetype}>(META_DATA_LOAD_DECL(${cppcrepr.metadataName}));`;
            const assign = `*${this.generateArgStore(cp.trgt)} = {${cargs.join(", ")}};`;

            return [...ops, alloc, assign];
        }
    }

    generateMIRConstructorPrimaryCollectionEmpty(cpce: MIRConstructorPrimaryCollectionEmpty): string {
        const cpetype = this.typegen.getMIRType(cpce.tkey);
        const cppctype = this.typegen.getCPPReprFor(cpetype).basetype;

        this.ensureLocationForTrgt(cpce.trgt);
        return `${this.generateArgStore(cpce.trgt)} = ${cppctype}::empty;`;
    }

    generateMIRConstructorPrimaryCollectionSingletons(cpcs: MIRConstructorPrimaryCollectionSingletons): string[] {
        const cpcstype = this.typegen.getMIRType(cpcs.tkey);
        const cpcsrepr = this.typegen.getCPPReprFor(cpcstype);

        let oftype = this.typegen.noneType;
        let extraalloc = 1;
        if (this.typegen.typecheckIsName(cpcstype, /^NSCore::List<.*>$/)) {
            oftype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
        }
        else if (this.typegen.typecheckIsName(cpcstype, /^NSCore::Stack<.*>$/)) {
            oftype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
        }
        else if (this.typegen.typecheckIsName(cpcstype, /^NSCore::Queue<.*>$/)) {
            oftype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
        }
        else if (this.typegen.typecheckIsName(cpcstype, /^NSCore::Set<.*>$/) || this.typegen.typecheckIsName(cpcstype, /^NSCore::DynamicSet<.*>$/)) {
            oftype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
            extraalloc = 2; //we may want to resize
        }
        else {
            const ktype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("K") as MIRType;
            const vtype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("V") as MIRType;

            const entrytype = [...this.typegen.assembly.entityDecls].find((edecl) => edecl[1].ns === "NSCore" && edecl[1].name === "MapEntry" && (edecl[1].terms.get("K") as MIRType).trkey === ktype.trkey && (edecl[1].terms.get("V") as MIRType).trkey === vtype.trkey);
            const entryentity = (entrytype as [string, MIREntityTypeDecl])[1];
            oftype = this.typegen.getMIRType(entryentity.tkey);
        }

        let argpairs: [MIRArgument, MIRType][] = [];
        for (let i = 0; i < cpcs.args.length; ++i) {
            argpairs.push([cpcs.args[i], oftype]);
        }

        const crepr = this.typegen.getCPPReprFor(oftype);
        const csize = cpcsrepr.alignedSize + StorageByteAlignment + (crepr.alignedSize * argpairs.length);

        const [cargs, ops] = this.coerceArgsInlinePlus(extraalloc * csize, ...argpairs);

        this.ensureLocationForTrgt(cpcs.trgt);
        let conscall = "[INVALID CONS CALL]";
        if (this.typegen.typecheckIsName(cpcstype, /^NSCore::List<.*>$/)) {
            conscall = `${this.generateArgStore(cpcs.trgt)} = BSQList<${crepr.storagetype}>::processSingletonInit<${cpcsrepr.basetype}, ${argpairs.length}>(META_DATA_LOAD_DECL(${crepr.metadataName}), {${cargs.join(", ")}});`;
        }
        else if (this.typegen.typecheckIsName(cpcstype, /^NSCore::Stack<.*>$/)) {
            conscall = `${this.generateArgStore(cpcs.trgt)} = BSQStack<${crepr.storagetype}>::processSingletonInit<${cpcsrepr.basetype}, ${argpairs.length}>(META_DATA_LOAD_DECL(${crepr.metadataName}), {${cargs.join(", ")}});`;
        }
        else if (this.typegen.typecheckIsName(cpcstype, /^NSCore::Queue<.*>$/)) {
            conscall = `${this.generateArgStore(cpcs.trgt)} = BSQQueue<${crepr.storagetype}>::processSingletonInit<${cpcsrepr.basetype}, ${argpairs.length}>(META_DATA_LOAD_DECL(${crepr.metadataName}), {${cargs.join(", ")}});`;
        }
        else if (this.typegen.typecheckIsName(cpcstype, /^NSCore::Set<.*>$/) || this.typegen.typecheckIsName(cpcstype, /^NSCore::DynamicSet<.*>$/)) {
            const tops = this.typegen.getFunctorsForType(oftype);

            conscall = `${this.generateArgStore(cpcs.trgt)} = BSQSet<${crepr.storagetype}, ${tops.less}, ${tops.eq}>::processSingletonInit<${cpcsrepr.basetype}, ${argpairs.length}>(META_DATA_LOAD_DECL(${crepr.metadataName}), {${cargs.join(", ")}});`;
        }
        else {
            const ktype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("K") as MIRType;
            const vtype = (this.assembly.entityDecls.get(cpcs.tkey) as MIREntityTypeDecl).terms.get("V") as MIRType;

            const krepr = this.typegen.getCPPReprFor(ktype);
            const kops = this.typegen.getFunctorsForType(ktype);
            const vrepr = this.typegen.getCPPReprFor(vtype);

            conscall = `${this.generateArgStore(cpcs.trgt)} = BSQMap<${krepr.storagetype}, ${vrepr.storagetype}, ${kops.less}, ${kops.eq}, ${crepr.storagetype}, KGET_${crepr.basetype}, VGET_${crepr.basetype}>::singletonInit<${cpcsrepr.basetype}, ${argpairs.length}(META_DATA_LOAD_DECL(${crepr.metadataName}), {${cargs.join(", ")}});`;
        }

        return [...ops, conscall];
    }

    generateMIRConstructorTuple(op: MIRConstructorTuple): string[] {
        if(op.args.length === 0) {
            //Other fields should be 0 filled by default through zerofill
            return [`${this.generateArgStore(op.trgt)}.flag = DATA_KIND_ALL_FLAG;`];
        }
        else {
            let argpairs: [MIRArgument, MIRType][] = [];
            for (let i = 0; i < op.args.length; ++i) {
                argpairs.push([op.args[i], this.typegen.anyType]);
            }

            const [cargs, ops] = this.coerceArgsInline(...argpairs);

            const trepr = this.typegen.getCPPReprFor(this.typegen.getMIRType(op.resultTupleType));
            const iflag = this.typegen.generateInitialDataKindFlag(this.typegen.getMIRType(op.resultTupleType));

            this.ensureLocationForTrgt(op.trgt);
            const ctuple = `${trepr.basetype}::createFromSingle<${iflag}>(${this.generateArgStore(op.trgt)}, { ${cargs.join(", ")} });`;

            return [...ops, ctuple];
        }
    }

    generateMIRConstructorRecord(op: MIRConstructorRecord): string[] {
        if(op.args.length === 0) {
            //Other fields should be 0 filled by default through zerofill
            return [`${this.generateArgStore(op.trgt)}.flag = DATA_KIND_ALL_FLAG;`];
        }
        else {
            let argpairs: [MIRArgument, MIRType][] = [];
            for (let i = 0; i < op.args.length; ++i) {
                argpairs.push([op.args[i][1], this.typegen.anyType]);
            }

            const [cargs, ops] = this.coerceArgsInline(...argpairs);

            const trepr = this.typegen.getCPPReprFor(this.typegen.getMIRType(op.resultRecordType));
            const iflag = this.typegen.generateInitialDataKindFlag(this.typegen.getMIRType(op.resultRecordType));

            const propertyset = `BSQPropertySet::knownRecordPropertySets[MIRRecordPropertySetsEnum::ps${trepr.basetype}].data()`

            this.ensureLocationForTrgt(op.trgt);
            const crecord = `${trepr.basetype}::createFromSingle<${iflag}>(${this.generateArgStore(op.trgt)}, ${propertyset}, { ${cargs.join(", ")} });`;

            return [...ops, crecord];
        }
    }

    generateMIRConstructorEphemeralValueList(op: MIRConstructorEphemeralValueList): string[] {
        const etype = this.typegen.getMIRType(op.resultEphemeralListType).options[0] as MIREphemeralListType;

        let argpairs: [MIRArgument, MIRType][] = [];
        for (let i = 0; i < op.args.length; ++i) {
            argpairs.push([op.args[i], etype.entries[i]]);
        }

        const [cargs, ops] = this.coerceArgsInline(...argpairs);

        this.ensureLocationForTrgt(op.trgt);
        const cephemeral = `${this.generateArgStore(op.trgt)} = { ${cargs.join(", ")} };`;

        return [...ops, cephemeral];
    }

    generateMIRProjectFromIndecies(op: MIRProjectFromIndecies, resultAccessType: MIRType): string[] {
        const intotypes = this.typegen.typecheckEphemeral(resultAccessType) ? (resultAccessType.options[0] as MIREphemeralListType).entries : [];

        let argpairs: [string, MIRType, MIRType][] = [];
        for (let i = 0; i < op.indecies.length; ++i) {
            argpairs.push([this.generateIndexExpression(op.arg, op.indecies[i]), this.typegen.anyType, intotypes[i] || this.typegen.anyType]);
        }

        const [cargs, ops] = this.coerceAccessInline(...argpairs);

        this.ensureLocationForTrgt(op.trgt);
        if (this.typegen.typecheckEphemeral(resultAccessType)) {
            const cephemeral = `${this.generateArgStore(op.trgt)} = { ${cargs.join(", ")} };`;

            return [...ops, cephemeral];
        }
        else {
            const iflag = this.typegen.generateInitialDataKindFlag(resultAccessType);
            const rrepr = this.typegen.getCPPReprFor(resultAccessType);
            const ctuple = `${rrepr.basetype}::createFromSingle<${iflag}>(${this.generateArgStore(op.trgt)}, { ${cargs.join(", ")} });`;

            return [...ops, ctuple];
        }
    }

    generateMIRModifyWithIndecies(op: MIRModifyWithIndecies, resultTupleType: MIRType): string[] {
        const updmax = Math.max(...op.updates.map((upd) => upd[0] + 1));

        let argpairs: [string, MIRType, MIRType][] = [];
        for (let i = 0; i < updmax; ++i) {
            const upd = op.updates.find((update) => update[0] === i);
            if (upd !== undefined) {
                argpairs.push([this.generateArgSrc(upd[1]), this.getArgType(upd[1]), this.typegen.anyType]);
            } 
            else {
                argpairs.push([this.generateIndexExpression(op.arg, i), this.typegen.anyType, this.typegen.anyType]);
            }
        }

        const rmax = this.typegen.getMaxTupleLength(resultTupleType);
        for (let i = updmax; i < rmax; ++i) {
            //may put none in the constructor list but ok since we note correct length and will ignore these if extranious
            argpairs.push([this.generateIndexExpression(op.arg, i), this.typegen.anyType, this.typegen.anyType]);
        }

        const [cargs, ops] = this.coerceAccessInline(...argpairs);

        const trepr = this.typegen.getCPPReprFor(resultTupleType);
        this.ensureLocationForTrgt(op.trgt);

        const iflag = this.typegen.generateInitialDataKindFlag(resultTupleType);
        const ctuple = `${trepr.basetype}::createFromSingle<${iflag}>(${this.generateArgStore(op.trgt)}, { ${cargs.join(", ")} });`;

        return [...ops, ctuple];
    }

    generateMIRStructuredExtendTuple(op: MIRStructuredExtendTuple, resultTupleType: MIRType): string[] {
         //this is the exact number of indecies in arg -- see typecheck
         const btuple = this.typegen.getMaxTupleLength(this.typegen.getMIRType(op.argInferType));

        let argpairs: [string, MIRType, MIRType][] = [];
        for (let i = 0; i < btuple; ++i) {
            argpairs.push([this.generateIndexExpression(op.arg, i), this.typegen.anyType, this.typegen.anyType]);
        }

        const rmax = this.typegen.getMaxTupleLength(resultTupleType);
        for (let i = btuple; i < rmax; ++i) {
            //may put none in the constructor list but ok since we note correct length and will ignore these if extranious
            argpairs.push([this.generateIndexExpression(op.update, i - btuple), this.typegen.anyType, this.typegen.anyType]);
        }

        const [cargs, ops] = this.coerceAccessInline(...argpairs);

        const trepr = this.typegen.getCPPReprFor(resultTupleType);
        this.ensureLocationForTrgt(op.trgt);

        const iflag = this.typegen.generateInitialDataKindFlag(resultTupleType);
        const ctuple = `${trepr.basetype}::createFromSingle<${iflag}>(${this.generateArgStore(op.trgt)}, { ${cargs.join(", ")} });`;

        return [...ops, ctuple];
    }

    generateMIRHasPropertyExpression(arg: MIRArgument, property: string): string {
        const rectype = this.getArgType(arg);
        const hasproperty = this.typegen.recordHasField(rectype, property);
    
        if(hasproperty === "no") {
            return "false";
        }
        else {
            const rrepr = this.typegen.getCPPReprFor(rectype);
            if(rrepr instanceof TRRepr) {
                return `${this.cppframe.getExpressionForName(this.varToCppName(arg))}.hasProperty<MIRPropertyEnum::${property}>()`;
            }
            else if (rrepr instanceof UnionRepr) {
                return `(UnionValue::extractPointerToContent<BSQRecordDynamic>(${this.cppframe.getExpressionForName(this.varToCppName(arg))})->hasProperty<${property}>()`;
            }
            else {
                return `((BSQTupleDynamic*)${this.cppframe.getExpressionForName(this.varToCppName(arg))})->hasProperty<${property}>()`;
            }
        }
    }

    generateMIRProjectFromProperties(op: MIRProjectFromProperties, resultAccessType: MIRType): string[] {
        const intotypes = this.typegen.typecheckEphemeral(resultAccessType) ? (resultAccessType.options[0] as MIREphemeralListType).entries : [];
       
        let argpairs: [string, MIRType, MIRType][] = [];
        for (let i = 0; i < op.properties.length; ++i) {
            argpairs.push([this.generatePropertyExpression(op.arg, op.properties[i]), this.typegen.anyType, intotypes[i] || this.typegen.anyType]);
        }

        const [cargs, ops] = this.coerceAccessInline(...argpairs);

        this.ensureLocationForTrgt(op.trgt);
        if (this.typegen.typecheckEphemeral(resultAccessType)) {
            const cephemeral = `${this.generateArgStore(op.trgt)} = { ${cargs.join(", ")} };`;

            return [...ops, cephemeral];
        }
        else {
            const iflag = this.typegen.generateInitialDataKindFlag(resultAccessType);
            const rrepr = this.typegen.getCPPReprFor(resultAccessType);
            const ctuple = `${rrepr.basetype}::createFromSingle<${iflag}>(${this.generateArgStore(op.trgt)}, { ${cargs.join(", ")} });`;

            return [...ops, ctuple];
        }
    }

    generateMIRModifyWithProperties(op: MIRModifyWithProperties, resultRecordType: MIRType): string[] {
        let argpairs: [string, MIRType, MIRType][] = [[this.generateArgSrc(op.arg), this.getArgType(op.arg), this.typegen.getMIRType(op.argInferType)]];
        for (let i = 0; i < op.updates.length; ++i) {
            argpairs.push([this.generateArgSrc(op.updates[i][1]), this.getArgType(op.updates[i][1]), this.typegen.anyType]);
        }

        const [cargs, ops] = this.coerceAccessInline(...argpairs);

        let updates: string[] = [];
        for (let i = 0; i < op.updates.length; ++i) {
            updates.push(`{ MIRPropertyEnum::${op.updates[0]}, ${cargs[i + 1]} }`);
        }

        const iflag = this.typegen.generateInitialDataKindFlag(resultRecordType);
        const rrepr = this.typegen.getCPPReprFor(resultRecordType);
        const crecord = `${rrepr.basetype}::createFromUpdate<${iflag}>(${this.generateArgStore(op.trgt)}, ${updates[0]}, { ${updates.join(", ")} });`;

        return [...ops, crecord];
    }

    generateMIRStructuredExtendRecord(op: MIRStructuredExtendRecord, resultRecordType: MIRType): string[] {
        let argpairs: [string, MIRType, MIRType][] = [
            [this.generateArgSrc(op.arg), this.getArgType(op.arg), this.typegen.getMIRType(op.argInferType)],
            [this.generateArgSrc(op.update), this.getArgType(op.update), this.typegen.getMIRType(op.updateInferType)]
        ];
        
        const [cargs, ops] = this.coerceAccessInline(...argpairs);

        const iflag = this.typegen.generateInitialDataKindFlag(resultRecordType);
        const rrepr = this.typegen.getCPPReprFor(resultRecordType);
        const crecord = `${rrepr.basetype}::createFromMerge<${iflag}>(${this.generateArgStore(op.trgt)}, ${cargs[0]}, ${cargs[1]});`;

        return [...ops, crecord];
    }

    generateVFieldLookup(op: MIRAccessFromField, resultAccessType: MIRType): string[] {
        return NOT_IMPLEMENTED<string[]>("generateVFieldLookup");
    }

    generateMIRAccessFromField(op: MIRAccessFromField, resultAccessType: MIRType): string[] {
        const inferargtype = this.typegen.getMIRType(op.argInferType);

        const fdecl = this.assembly.fieldDecls.get(op.field) as MIRFieldDecl;
        const ftype = this.typegen.getMIRType(fdecl.declaredType);

        if (this.typegen.typecheckUEntity(inferargtype)) {
            const access = this.generateFieldExpressionKnown(op.arg, inferargtype, fdecl.fkey);

            this.ensureLocationForTrgt(op.trgt);
            return this.coerceResult(access, ftype, this.generateArgStore(op.trgt), resultAccessType);
        }
        else {
            return this.generateVFieldLookup(op, resultAccessType);
        }
    }

    generateVFieldProject(op: MIRProjectFromFields, resultAccessType: MIRType): string[] {
        return NOT_IMPLEMENTED<string[]>("generateVFieldProject");
    }

    generateMIRProjectFromFields(op: MIRProjectFromFields, resultAccessType: MIRType): string[] {
        const inferargtype = this.typegen.getMIRType(op.argInferType);
        if(this.typegen.typecheckUEntity(inferargtype)) {
            const intotypes = this.typegen.typecheckEphemeral(resultAccessType) ? (resultAccessType.options[0] as MIREphemeralListType).entries : [];
       
            let vfpops: string[] = [];
            let argpairs: [string, MIRType, MIRType][] = [];
            for (let i = 0; i < op.fields.length; ++i) {
                const fdecl = this.assembly.fieldDecls.get(op.fields[i]) as MIRFieldDecl;
                const ftype = this.typegen.getMIRType(fdecl.declaredType);
                const intotype = intotypes[i] || this.typegen.anyType;

                argpairs.push([this.generateFieldExpressionKnown(op.arg, inferargtype, op.fields[i]), ftype, intotype]);
            }

            const [cargs, ops] = this.coerceAccessInline(...argpairs);

            this.ensureLocationForTrgt(op.trgt);
            const cephemeral = `${this.generateArgStore(op.trgt)} = { ${cargs.join(", ")} };`;

            return [...vfpops, ...ops, cephemeral];
        }
        else {
           return this.generateVFieldProject(op, resultAccessType);
        }
    }

    generateVCallModifyField(op: MIRModifyWithFields, resultAccessType: MIRType): string[] {
        return NOT_IMPLEMENTED<string[]>("generateVCallModifyField");
    }

    generateMIRModifyWithFields(op: MIRModifyWithFields, resultAccessType: MIRType): string[] {
        const inferargtype = this.typegen.getMIRType(op.argInferType);

        if(this.typegen.typecheckUEntity(inferargtype)) {
            const inferrepr = this.typegen.getCPPReprFor(inferargtype);
            const ekey = this.typegen.getEntityEKey(inferargtype);
            const utype = this.typegen.assembly.entityDecls.get(ekey) as MIREntityTypeDecl;

            let argpairs: [string, MIRType, MIRType][] = [];
            for (let i = 0; i < utype.fields.length; ++i) {
                const fdecl = utype.fields[i];
                const ftype = this.typegen.getMIRType(fdecl.declaredType);

                const upd = op.updates.find((update) => update[0] == fdecl.fkey);
                if(upd !== undefined) {
                    argpairs.push([this.generateArgSrc(upd[1]), this.getArgType(upd[1]), ftype]);
                }
                else {
                    argpairs.push([this.generateFieldExpressionKnown(op.arg, inferargtype, fdecl.fkey), ftype, ftype]);
                }
            }

            this.ensureLocationForTrgt(op.trgt);
            const [cargs, ops] = this.coerceAccessInlinePlus(inferrepr.alignedSize + StorageByteAlignment, ...argpairs);
           
            if(inferrepr instanceof StructRepr) {
                const assign = `${this.generateArgStore(op.trgt)} = { ${cargs.join(", ")} };`;

                return [...ops, assign];
            }
            else {
                const alloc = `${this.generateArgStore(op.trgt)} = Allocator::GlobalAllocator.allocateSafe<${inferrepr.basetype}>(META_DATA_LOAD_DECL(${inferrepr.metadataName});`;
                const assign = `*${this.generateArgSrc(op.trgt)} = = { ${cargs.join(", ")} };`;

                return [...ops, alloc, assign];
            }
        }
        else {
            return this.generateVCallModifyField(op, resultAccessType);
        }
    }

    generateVFieldExtend(op: MIRStructuredExtendObject, resultAccessType: MIRType): string[] {
        return NOT_IMPLEMENTED<string[]>("generateVFieldExtend");
    }

    generateMIRStructuredExtendObject(op: MIRStructuredExtendObject, resultAccessType: MIRType): string[] {
        const inferargtype = this.typegen.getMIRType(op.argInferType);
        const mergeargtype = this.typegen.getMIRType(op.updateInferType);
        
        if (this.typegen.typecheckUEntity(inferargtype)) {
            const inferrepr = this.typegen.getCPPReprFor(inferargtype);
            const ekey = this.typegen.getEntityEKey(inferargtype);
            const utype = this.typegen.assembly.entityDecls.get(ekey) as MIREntityTypeDecl;

            let argpairs: [string, MIRType, MIRType][] = [];
            for (let i = 0; i < utype.fields.length; ++i) {
                const fdecl = utype.fields[i];
                const ftype = this.typegen.getMIRType(fdecl.declaredType);

                const fp = op.fieldResolves.find((tfp) => tfp[1] === fdecl.fkey) as [string, MIRFieldKey];
                const faccess = [this.generateFieldExpressionKnown(op.arg, inferargtype, fdecl.fkey), ftype, ftype] as [string, MIRType, MIRType];
                const paccess = [this.generatePropertyExpression(op.arg, fp[0]), this.typegen.anyType, ftype] as [string, MIRType, MIRType];
                const hasp = this.typegen.recordHasField(mergeargtype, fp[0]);
                if(hasp === "no") {
                    argpairs.push(faccess);
                }
                else if (hasp === "yes") {
                    argpairs.push(paccess);
                }
                else {
                    argpairs.push(paccess);
                    argpairs.push(faccess);
                }
            }

            this.ensureLocationForTrgt(op.trgt);
            const [cargs, ops] = this.coerceAccessInlinePlus(inferrepr.alignedSize + StorageByteAlignment, ...argpairs);

            let rargs: string[] = [];
            let argpos = 0;
            for (let i = 0; i < utype.fields.length; ++i) {
                const fdecl = utype.fields[i];
                const fp = op.fieldResolves.find((tfp) => tfp[1] === fdecl.fkey) as [string, MIRFieldKey];
                const hasp = this.typegen.recordHasField(mergeargtype, fp[0]);

                if(hasp === "no" || hasp == "yes") {
                    rargs.push(cargs[argpos++]);
                }
                else {
                    const check = this.generateMIRHasPropertyExpression(op.update, fp[0]);
                    const update = `(${check} ? ${cargs[argpos]}) : ${cargs[argpos + 1]})`;

                    rargs.push(update);
                    argpos += 2;
                }
            }

            if(inferrepr instanceof StructRepr) {
                const assign = `${this.generateArgStore(op.trgt)} = { ${rargs.join(", ")} };`;

                return [...ops, assign];
            }
            else {
                const alloc = `${this.generateArgStore(op.trgt)} = Allocator::GlobalAllocator.allocateSafe<${inferrepr.basetype}>(META_DATA_LOAD_DECL(${inferrepr.metadataName});`;
                const assign = `*${this.generateArgSrc(op.trgt)} = = { ${rargs.join(", ")} };`;

                return [...ops, alloc, assign];
            }
        }
        else {
            return this.generateVFieldExtend(op, resultAccessType);
        }
    }

    generateMIRLoadFromEpehmeralList(op: MIRLoadFromEpehmeralList): string {
        return `${this.varToCppName(op.trgt)} = ${this.varToCppName(op.arg)}.entry_${op.idx};`;
    }

    generateMIRInvokeFixedFunction(ivop: MIRInvokeFixedFunction): string[] {
        const idecl = (this.assembly.invokeDecls.get(ivop.mkey) || this.assembly.primitiveInvokeDecls.get(ivop.mkey)) as MIRInvokeDecl;

        this.ensureLocationForTrgt(ivop.trgt);
        return this.generateInvokeInto(this.generateArgStore(ivop.trgt), this.getArgType(ivop.trgt), idecl, ivop.args);

    }

    generateEquals(op: string, lhsinfertype: MIRType, lhs: MIRArgument, rhsinfertype: MIRType, rhs: MIRArgument, isstrict: boolean): [string[], string] {
        if (isstrict) {
            const repr = this.typegen.getCPPReprFor(lhsinfertype);
            const [cargs, ops] = this.coerceArgsInline([lhs, lhsinfertype], [rhs, rhsinfertype]);

            return [ops, (op === "!=" ? "!" : "") + `EqualFunctor_${repr.basetype}{}(${cargs[0]}, ${cargs[1]})`];
        }
        else {
            const [cargs, ops] = this.coerceArgsInline([lhs, this.typegen.keyType], [rhs, this.typegen.keyType]);

            return [ops, (op === "!=" ? "!" : "") + `EqualFunctor_KeyValue{}(${cargs[0]}, ${cargs[1]})`];
        }
    }

    generateLess(lhsinfertype: MIRType, lhs: MIRArgument, rhsinfertype: MIRType, rhs: MIRArgument, isstrict: boolean): [string[], string] {
        if (isstrict) {
            const repr = this.typegen.getCPPReprFor(lhsinfertype);
            const [cargs, ops] = this.coerceArgsInline([lhs, lhsinfertype], [rhs, rhsinfertype]);

            return [ops, `LessFunctor_${repr.basetype}{}(${cargs[0]}, ${cargs[1]})`];
        }
        else {
            const [cargs, ops] = this.coerceArgsInline([lhs, this.typegen.keyType], [rhs, this.typegen.keyType]);

            return [ops, `LessFunctor_KeyValue{}(${cargs[0]}, ${cargs[1]})`];
        }
    }

    generateCompare(op: string, lhsinfertype: MIRType, lhs: MIRArgument, rhsinfertype: MIRType, rhs: MIRArgument): [string[], string] {
        if (op === "<") {
            return this.generateLess(lhsinfertype, lhs, rhsinfertype, rhs, true);
        }
        else if (op === "<=") {
            const lessop = this.generateLess(lhsinfertype, lhs, rhsinfertype, rhs, true);
            const eqop = this.generateEquals("=", lhsinfertype, lhs, rhsinfertype, rhs, true);
            return [[...lessop[0], ...eqop[0]], `${lessop[1]} || ${eqop[1]}`];
        }
        else if (op === ">") {
            return this.generateLess(rhsinfertype, rhs, lhsinfertype, lhs, true);
        }
        else {
            const lessop = this.generateLess(rhsinfertype, rhs, lhsinfertype, lhs, true);
            const eqop = this.generateEquals("=", rhsinfertype, rhs, lhsinfertype, lhs, true);
            return [[...lessop[0], ...eqop[0]], `${lessop[1]} || ${eqop[1]}`];
        }
    }

    generateSubtypeTupleCheck(argv: string, argtype: MIRType, oftype: MIRTupleType): string {
        const argrepr = this.typegen.getCPPReprFor(argtype);
        const subtypesig = `bool subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}_TTC(${argrepr.passingtype} arg)`;

        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            let ttuple = "";
            if (argrepr instanceof TRRepr) {
                ttuple = `BSQDynamicTuple* tt = &arg;`;
            }
            else if (argrepr instanceof UnionRepr) {
                ttuple = `BSQDynamicTuple* tt = ${argrepr.basetype}::extractPointerToContent<BSQDynamicTuple>(arg);`;
            }
            else {
                ttuple = `BSQDynamicTuple* tt = (BSQDynamicTuple*)arg;`;
            }

            let checks: string[] = [];

            checks.push(`(tt->count <= ${oftype.entries.length})`);

            //do all the checks that argtype satisfies all the requirements of oftype -- maybe a bit inefficiently
            for (let i = 0; i < oftype.entries.length; ++i) {
                const chk = this.generateTypeCheck(`tt->atFixed<${i}>()`, this.typegen.anyType, this.typegen.anyType, oftype.entries[i].type);

                if(oftype.entries[i].isOptional) {
                    checks.push(`(!tt->hasIndex<${i}>() || ${chk})`);
                }
                else {
                    checks.push(`tt->hasIndex<${i}>()`);
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
            + `    ${ttuple}\n`
            + `    return ${op};\n`
            + `}\n`;

            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }

        return `subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}_TTC(${argv})`;
    }

    generateTupleSpecialConceptCheck(argv: string, argtype: MIRType, oftype: MIRConceptType): string {
        const argrepr = this.typegen.getCPPReprFor(argtype);
        const subtypesig = `bool subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}_TSC(${argrepr.passingtype} arg)`;

        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            let ttuple = "";
            if (argrepr instanceof TRRepr) {
                ttuple = `BSQDynamicTuple* tt = &arg;`;
            }
            else if (argrepr instanceof UnionRepr) {
                ttuple = `BSQDynamicTuple* tt = ${argrepr.basetype}::extractPointerToContent<BSQDynamicTuple>(arg);`;
            }
            else {
                ttuple = `BSQDynamicTuple* tt = (BSQDynamicTuple*)arg;`;
            }

            const checks: string[] = [];
            if (oftype.ckeys.some((cc) => this.typegen.assembly.subtypeOf(this.typegen.parsableType, this.typegen.getMIRType(cc)))) {
                checks.push(`DATA_KIND_PARSABLE_FLAG`);
            }

            if (oftype.ckeys.some((cc) => this.typegen.assembly.subtypeOf(this.typegen.podType, this.typegen.getMIRType(cc)))) {
                checks.push(`DATA_KIND_POD_FLAG`);
            }

            if (oftype.ckeys.some((cc) => this.typegen.assembly.subtypeOf(this.typegen.apiType, this.typegen.getMIRType(cc)))) {
                checks.push(`DATA_KIND_POD_FLAG`);
            }

            const decl = subtypesig
            + "\n{\n"
            + `    ${ttuple}\n`
            + `    DATA_KIND_FLAG cf = (${checks.join(" | ")});\n`
            + `    return cf == (cf & tt->flag);\n`
            + `}\n`;

            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }

        return `subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}_TSC(${argv})`;
    }

    generateSubtypeRecordCheck(argv: string, argtype: MIRType, oftype: MIRRecordType): string {
        const argrepr = this.typegen.getCPPReprFor(argtype);
        const subtypesig = `bool subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}_TRC(${argrepr.passingtype} arg)`;

        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            let trecord = "";
            if (argrepr instanceof StructRepr) {
                trecord = `BSQDynamicRecord* tr = &arg;`;
            }
            else if (argrepr instanceof UnionRepr) {
                trecord = `BSQDynamicRecord* tr = ${argrepr.basetype}::extractPointerToContent<BSQDynamicRecord>(arg);`;
            }
            else {
                trecord = `BSQDynamicRecord* tr = (BSQDynamicRecord*)arg;`;
            }

            let checks: string[] = [];

            //do all the checks that argtype satisfies all the requirements of oftype -- maybe a bit inefficiently
            for (let i = 0; i < oftype.entries.length; ++i) {
                const pname = oftype.entries[i].name;
                const chk = this.generateTypeCheck(`tr->atFixed<MIRPropertyEnum::${pname}>()`, this.typegen.anyType, this.typegen.anyType, oftype.entries[i].type);

                if (oftype.entries[i].isOptional) {
                    checks.push(`(!tr->hasProperty<MIRPropertyEnum::${pname}>() || ${chk})`);
                }
                else {
                    checks.push(`tr->hasProperty<MIRPropertyEnum::${pname}>()`);
                    checks.push(chk);
                }
            }

            //do checks that argtype doesn't have any other properties
            if (this.typegen.typecheckRecord(argtype)) {
                const allprops = this.typegen.getMaxPropertySet(argtype);

                for (let i = 0; i < allprops.length; ++i) {
                    const pname = allprops[i];
                    if (oftype.entries.find((entry) => entry.name === pname) === undefined) {
                        checks.push(`!tr->hasProperty<MIRPropertyEnum::${pname}>()`);
                    }
                }
            }
            else {
                const pprops = oftype.entries.map((entry) => `MIRPropertyEnum::${entry.name}`);
                checks.push(`tr->checkPropertySet(${oftype.entries.length}${oftype.entries.length !== 0 ? ", " : ""} ${pprops.join(", ")})`);
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
            + `    ${trecord}\n`
            + `    return ${op};\n`
            + `}\n`;

            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }

        return `subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}_TRC(${argv})`;
    }

    generateRecordSpecialConceptCheck(argv: string, argtype: MIRType, oftype: MIRConceptType): string {
        const argrepr = this.typegen.getCPPReprFor(argtype);
        const subtypesig = `bool subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}_RSC(${argrepr.passingtype} arg)`;

        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            let trecord = "";
            if (argrepr instanceof StructRepr) {
                trecord = `BSQDynamicRecord* tr = &arg;`;
            }
            else if (argrepr instanceof UnionRepr) {
                trecord = `BSQDynamicRecord* tr = ${argrepr.basetype}::extractPointerToContent<BSQDynamicRecord>(arg);`;
            }
            else {
                trecord = `BSQDynamicRecord* tr = BSQ_GET_VALUE_PTR(arg, BSQRecord);`;
            }

            const checks: string[] = [];
            if (oftype.ckeys.some((cc) => this.typegen.assembly.subtypeOf(this.typegen.parsableType, this.typegen.getMIRType(cc)))) {
                checks.push(`DATA_KIND_PARSABLE_FLAG`);
            }

            if (oftype.ckeys.some((cc) => this.typegen.assembly.subtypeOf(this.typegen.podType, this.typegen.getMIRType(cc)))) {
                checks.push(`DATA_KIND_POD_FLAG`);
            }

            if (oftype.ckeys.some((cc) => this.typegen.assembly.subtypeOf(this.typegen.apiType, this.typegen.getMIRType(cc)))) {
                checks.push(`DATA_KIND_POD_FLAG`);
            }

            const decl = subtypesig
            + "\n{\n"
            + `    ${trecord}\n`
            + `    DATA_KIND_FLAG cf = (${checks.join(" | ")});\n`
            + `    return cf == (cf & tr->flag);\n`
            + `}\n`;

            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }

        return `subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}_RSC(${argv})`;
    }

    generateFastTupleTypeCheck(arg: string, argtype: MIRType, inferargtype: MIRType, oftype: MIRTupleType): string {
        if (!inferargtype.options.some((opt) => opt instanceof MIRTupleType)) {
            return "false";
        }
        else {
            const argrepr = this.typegen.getCPPReprFor(argtype);
            const tsc = this.generateSubtypeTupleCheck(arg, argtype, oftype);

            if (argrepr instanceof StructRepr) {
                return tsc;
            }
            else {
                return `(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQTuple*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr && ${tsc})`;
            }
        }
    }

    generateFastRecordTypeCheck(arg: string, argtype: MIRType, inferargtype: MIRType, oftype: MIRRecordType): string {
        if (!inferargtype.options.some((opt) => opt instanceof MIRRecordType)) {
            return "false";
        }
        else {
            const argrepr = this.typegen.getCPPReprFor(argtype);
            const tsc = this.generateSubtypeTupleCheck(arg, argtype, oftype);

            if (argrepr instanceof StructRepr) {
                return tsc;
            }
            else {
                return `(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQRecord*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr && ${tsc})`;
            }
        }
    }

    generateSubtypeArrayLookup(typeenum: string, oftype: MIRConceptType): string {
        this.checkedConcepts.add(oftype.trkey);
        const arraystr = `MIRConceptSubtypeArray__${this.typegen.mangleStringForCpp(oftype.trkey)}`;
        return `BSQObject::checkSubtype(${typeenum}, ${arraystr})`;
    }

    generateFastConceptTypeCheck(arg: string, argtype: MIRType, inferargtype: MIRType, oftype: MIRConceptType): string {
        if (this.typegen.typecheckIsName(inferargtype, /^NSCore::None$/) || this.typegen.typecheckUEntity(inferargtype)) {
            return this.typegen.assembly.subtypeOf(inferargtype, this.typegen.getMIRType(oftype.trkey)) ? "true" : "false";
        }
        else {
            let enumacc = "";
            if (this.typegen.typecheckTuple(inferargtype)) {
                enumacc = "MIRNominalTypeEnum_Tuple";
            }
            else if (this.typegen.typecheckRecord(inferargtype)) {
                enumacc = "MIRNominalTypeEnum_Record";
            }
            else {
                const argrepr = this.typegen.getCPPReprFor(argtype);
                if(argrepr instanceof RefRepr) {
                    enumacc = `${arg} === null ? MIRNominalTypeEnum_None : GET_TYPE_META_DATA(${arg})->nominaltype`;
                }
                else if (argrepr instanceof UnionRepr) {
                    enumacc = `${arg}.umeta->nominaltype`;
                }
                else {
                    enumacc = `GET_TYPE_META_DATA(${arg})->nominaltype`;
                }
            }

            let ttest = "false";
            if (inferargtype.options.some((iopt) => iopt instanceof MIRTupleType)) {
                const tupmax = MIRType.createSingle(MIRConceptType.create([this.typegen.tupleType.trkey, this.typegen.podType.trkey, this.typegen.parsableType.trkey]));
                const maybespecial = this.typegen.assembly.subtypeOf(tupmax, this.typegen.getMIRType(oftype.trkey)); //if this isn't true then special subtype will never be true
                const trival = this.typegen.assembly.subtypeOf(this.typegen.tupleType, this.typegen.getMIRType(oftype.trkey)); //if this is true then the default subtypeArray is enough
                if (maybespecial && !trival) {
                   ttest = `(enumacc == MIRNominalTypeEnum_Tuple) && ${this.generateTupleSpecialConceptCheck(arg, argtype, oftype)}`;
                }
            }

            let rtest = "false";
            if (inferargtype.options.some((iopt) => iopt instanceof MIRRecordType)) {
                const recmax = MIRType.createSingle(MIRConceptType.create([this.typegen.recordType.trkey, this.typegen.podType.trkey, this.typegen.parsableType.trkey]));
                const maybespecial = this.typegen.assembly.subtypeOf(recmax, this.typegen.getMIRType(oftype.trkey)); //if this isn't true then special subtype will never be true
                const trival = this.typegen.assembly.subtypeOf(this.typegen.recordType, this.typegen.getMIRType(oftype.trkey)); //if this is true then the default subtypeArray is enough
                if (maybespecial && !trival) {
                    rtest = `(enumacc == MIRNominalTypeEnum_Record) && ${this.generateRecordSpecialConceptCheck(arg, argtype, oftype)})`;
                }
            }

            const ntest = this.generateSubtypeArrayLookup(enumacc, oftype);

            const tests = [ntest, ttest, rtest].filter((test) => test !== "false");

            if (tests.length === 0) {
                return "false";
            }
            else if (tests.includes("true")) {
                return "true";
            }
            else if (tests.length === 1) {
                return tests[0];
            }
            else {
                return `(${tests.join(" || ")})`
            }
        }
    }

    generateFastEntityTypeCheck(arg: string, argtype: MIRType, inferargtype: MIRType, oftype: MIREntityType): string {
        if (this.typegen.typecheckIsName(inferargtype, /^NSCore::None$/) || this.typegen.typecheckUEntity(inferargtype)) {
            return inferargtype.trkey == oftype.trkey ? "true" : "false";
        }
        if (this.typegen.typecheckTuple(inferargtype)) {
            return "false";
        }
        else if (this.typegen.typecheckRecord(inferargtype)) {
            return "false";
        }
        else {
            const argrepr = this.typegen.getCPPReprFor(argtype);

            let enumacc = "";
            if(argrepr instanceof RefRepr) {
                enumacc = `${arg} === null ? MIRNominalTypeEnum_None : GET_TYPE_META_DATA(${arg})->nominaltype`;
            }
            else if (argrepr instanceof UnionRepr) {
                enumacc = `${arg}.umeta->nominaltype`;
            }
            else {
                enumacc = `GET_TYPE_META_DATA(${arg})->nominaltype`;
            }

            return `(${enumacc} == MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(oftype.ekey)})`;
        }
    }

    generateEphemeralTypeCheck(argv: string, argtype: MIRType, oftype: MIREphemeralListType): string {
        const argrepr = this.typegen.getCPPReprFor(argtype);
        const subtypesig = `bool subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}_EL(${argrepr.passingtype} arg)`;

        if (!this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            let checks: string[] = [];

            //do all the checks that argtype satisfies all the requirements of oftype 
            for (let i = 0; i < oftype.entries.length; ++i) {
                const etype = (argtype.options[0] as MIREphemeralListType).entries[i];
                checks.push(this.generateTypeCheck(`arg.entry_${i}`, etype, etype, oftype.entries[i]));
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

        return `subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}_EL(${argv})`;
    }

    generateTypeCheck(arg: string, argtype: MIRType, inferargtype: MIRType, oftype: MIRType): string {
        if(this.typegen.assembly.subtypeOf(inferargtype, oftype)) {
            //this case also include oftype == Any
            return "true";
        }
        const argrepr = this.typegen.getCPPReprFor(argtype);

        if(oftype.trkey === "NSCore::Some") {
            if(!this.typegen.assembly.subtypeOf(this.typegen.noneType, inferargtype)) {
                return "true";
            }
            else {
                if (argrepr instanceof NoneRepr) {
                    return "false";
                }
                else if (argrepr instanceof RefRepr || argrepr instanceof StructRepr) {
                    return "true";
                }
                else {
                    return `BSQ_IS_VALUE_NONNONE(${arg})`;
                }
            }
        }

        const tests = oftype.options.map((topt) => {
            const mtype = this.typegen.getMIRType(topt.trkey);
            assert(mtype !== undefined, "We should generate all the component types by default??");

            if(topt instanceof MIREntityType) {
                return this.generateFastEntityTypeCheck(arg, argtype, inferargtype, topt);
            }
            else if (topt instanceof MIRConceptType) {
                return this.generateFastConceptTypeCheck(arg, argtype, inferargtype, topt);
            }
            else if (topt instanceof MIRTupleType) {
                return this.generateFastTupleTypeCheck(arg, argtype, inferargtype, topt);
            }
            else if (topt instanceof MIRRecordType) {
                return this.generateFastRecordTypeCheck(arg, argtype, inferargtype, topt);
            }
            else {
                assert(topt instanceof MIREphemeralListType);

                return this.generateEphemeralTypeCheck(arg, argtype, topt as MIREphemeralListType);
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

    generateMIRPackSlice(op: MIRPackSlice): string {
        const etype = this.typegen.getMIRType(op.sltype).options[0] as MIREphemeralListType;

        let args: string[] = [];
        for(let i = 0; i < etype.entries.length; ++i) {
            args.push(`${this.varToCppName(op.src)}.entry_${i}`);
        }

        this.ensureLocationForTrgt(op.trgt);
        return `${this.generateArgStore(op.trgt)} = ${this.typegen.mangleStringForCpp(etype.trkey)}{ ${args.join(", ")} };`;
    }

    generateMIRPackSliceExtend(op: MIRPackExtend): string[] {
        const fromtype = this.getArgType(op.basepack).options[0] as MIREphemeralListType;
        const etype = this.typegen.getMIRType(op.sltype).options[0] as MIREphemeralListType;

        let args: string[] = [];
        for(let i = 0; i < fromtype.entries.length; ++i) {
            args.push(`${this.varToCppName(op.basepack)}.entry_${i}`);
        }

        let argpairs: [MIRArgument, MIRType][] = [];
        for (let i = 0; i < op.ext.length; ++i) {
            argpairs.push([op.ext[i], etype.entries[fromtype.entries.length + i]]);
        }
        const [cargs, ops] = this.coerceArgsInline(...argpairs);

        this.ensureLocationForTrgt(op.trgt);
        return [...ops, `${this.generateArgStore(op.trgt)} = ${this.typegen.mangleStringForCpp(etype.trkey)}{${[...args, ...cargs].join(", ")}};`];
    }

    generateStmt(op: MIROp): string[] {
        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const lcv = op as MIRLoadConst;
                this.ensureLocationForTrgt(lcv.trgt);
                return this.coerceResult(this.getConstantSrc(lcv.src), this.getArgType(lcv.src), this.generateArgStore(lcv.trgt), this.getArgType(lcv.trgt));
            }
            case MIROpTag.MIRLoadConstSafeString: {
                return [this.generateLoadConstSafeString(op as MIRLoadConstSafeString)];
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
                this.ensureLocationForTrgt(lav.trgt);
                return this.coerceResult(this.generateArgSrc(lav.name), this.getArgType(lav.name), this.generateArgStore(lav.trgt), this.getArgType(lav.trgt));
            }
            case MIROpTag.MIRAccessLocalVariable: {
                const llv = op as MIRAccessLocalVariable;
                this.ensureLocationForTrgt(llv.trgt);
                return this.coerceResult(this.generateArgSrc(llv.name), this.getArgType(llv.name), this.generateArgStore(llv.trgt), this.getArgType(llv.trgt));
            }
            case MIROpTag.MIRInvokeInvariantCheckDirect: {
                const icd = op as MIRInvokeInvariantCheckDirect;
                return [this.generateMIRInvokeInvariantCheckDirect(icd)];
            }
            case MIROpTag.MIRInvokeInvariantCheckVirtualTarget: {
                return NOT_IMPLEMENTED<string[]>("MIRInvokeInvariantCheckVirtualTarget");
            }
            case MIROpTag.MIRConstructorPrimary: {
                const cp = op as MIRConstructorPrimary;
                return this.generateMIRConstructorPrimary(cp);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
                const cpce = op as MIRConstructorPrimaryCollectionEmpty;
                return [this.generateMIRConstructorPrimaryCollectionEmpty(cpce)];
            }
            case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                const cpcs = op as MIRConstructorPrimaryCollectionSingletons;
                return this.generateMIRConstructorPrimaryCollectionSingletons(cpcs);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionCopies: {
                return NOT_IMPLEMENTED<string[]>("MIRConstructorPrimaryCollectionCopies");
            }
            case MIROpTag.MIRConstructorPrimaryCollectionMixed: {
                return NOT_IMPLEMENTED<string[]>("MIRConstructorPrimaryCollectionMixed");
            }
            case MIROpTag.MIRConstructorTuple: {
                return this.generateMIRConstructorTuple(op as MIRConstructorTuple);
            }
            case MIROpTag.MIRConstructorRecord: {
               return this.generateMIRConstructorRecord(op as MIRConstructorRecord);
            }
            case MIROpTag.MIRConstructorEphemeralValueList: {
                return this.generateMIRConstructorEphemeralValueList(op as MIRConstructorEphemeralValueList);
            }
            case MIROpTag.MIRAccessFromIndex: {
                const ai = op as MIRAccessFromIndex;
                this.ensureLocationForTrgt(ai.trgt);
                return this.coerceResult(this.generateIndexExpression(ai.arg, ai.idx), this.typegen.getMIRType(ai.resultAccessType), this.generateArgStore(ai.trgt), this.getArgType(ai.trgt));
            }
            case MIROpTag.MIRProjectFromIndecies: {
                const pi = op as MIRProjectFromIndecies;
                return this.generateMIRProjectFromIndecies(pi, this.typegen.getMIRType(pi.resultProjectType));
            }
            case MIROpTag.MIRAccessFromProperty: {
                const ap = op as MIRAccessFromProperty;
                this.ensureLocationForTrgt(ap.trgt);
                return this.coerceResult(this.generatePropertyExpression(ap.arg, ap.property), this.typegen.getMIRType(ap.resultAccessType), this.generateArgStore(ap.trgt), this.getArgType(ap.trgt));
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
                return this.generateMIRProjectFromFields(pf, this.typegen.getMIRType(pf.resultProjectType));
            }
            case MIROpTag.MIRProjectFromTypeTuple: {
                return NOT_IMPLEMENTED<string[]>("MIRProjectFromTypeTuple");
            }
            case MIROpTag.MIRProjectFromTypeRecord: {
                return NOT_IMPLEMENTED<string[]>("MIRProjectFromTypeRecord");
            }
            case MIROpTag.MIRProjectFromTypeNominal: {
                return NOT_IMPLEMENTED<string[]>("MIRProjectFromTypeNominal");
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
                return [this.generateMIRLoadFromEpehmeralList(le)];
            }
            case MIROpTag.MIRInvokeFixedFunction: {
                const invk = op as MIRInvokeFixedFunction;
                return this.generateMIRInvokeFixedFunction(invk);
            }
            case MIROpTag.MIRInvokeVirtualTarget: {
                return NOT_IMPLEMENTED<string[]>("MIRInvokeVirtualTarget");
            }
            case MIROpTag.MIRPrefixOp: {
                const pfx = op as MIRPrefixOp;
                if (pfx.op === "!") {
                    return `${this.varToCppName(pfx.trgt)} = !${this.argToCpp(pfx.arg, this.typegen.boolType)};`;
                }
                else {
                    if (pfx.op === "-") {
                        if (pfx.arg instanceof MIRConstantInt) {
                            return `${this.varToCppName(pfx.trgt)} = -${(pfx.arg as MIRConstantInt).value};`;
                        }
                        else if (pfx.arg instanceof MIRConstantBigInt) {
                            const scope = this.typegen.mangleStringForCpp("$scope$");
                            return `${this.varToCppName(pfx.trgt)} = BSQ_NEW_ADD_SCOPE(${scope}, BSQBigInt, "-${(pfx.arg as MIRConstantBigInt).digits()}");`;
                        }
                        else if (pfx.arg instanceof MIRConstantFloat64) {
                            return `${this.varToCppName(pfx.trgt)} = -${(pfx.arg as MIRConstantFloat64).digits()};`;
                        }
                        else {
                            const opt = this.typegen.getMIRType(pfx.infertype);
                            
                            if (this.typegen.typecheckIsName(opt, /^NSCore::Int$/)) {
                                return `${this.varToCppName(pfx.trgt)} = -${this.argToCpp(pfx.arg, this.typegen.intType)};`;
                            }
                            else if (this.typegen.typecheckIsName(opt, /^NSCore::BigInt$/)) {
                                const scope = this.typegen.mangleStringForCpp("$scope$");
                                return `${this.varToCppName(pfx.trgt)} = BSQBigInt::negate(${scope}, ${this.argToCpp(pfx.arg, this.typegen.bigIntType)});`;
                            }
                            else {
                                return `${this.varToCppName(pfx.trgt)} = -${this.argToCpp(pfx.arg, this.typegen.float64Type)};`;
                            }
                        }
                    }
                    else {
                        return `${this.varToCppName(pfx.trgt)} = ${this.argToCpp(pfx.arg, this.getArgType(pfx.trgt))};`;
                    }
                }
            }
            case MIROpTag.MIRBinOp: {
                const bop = op as MIRBinOp;
                const opt = this.typegen.getMIRType(bop.lhsInferType);

                if (this.typegen.typecheckIsName(opt, /^NSCore::Int$/)) {
                    if(bop.op !== "/") {
                        const chkedop = new Map<string, string>().set("+", "__builtin_add_overflow").set("-", "__builtin_sub_overflow").set("*", "__builtin_mul_overflow").get(bop.op) as string;
                        const opp = `if(${chkedop}(${this.argToCpp(bop.lhs, this.typegen.intType)}, ${this.argToCpp(bop.rhs, this.typegen.intType)}, &${this.varToCppName(bop.trgt)}) || INT_OOF_BOUNDS(${this.varToCppName(bop.trgt)})) { BSQ_ABORT("Int Overflow", "${filenameClean(this.currentFile)}", ${bop.sinfo.line}); }`;
                        return opp;
                    }
                    else {
                        const chk = `if(${this.argToCpp(bop.rhs, this.typegen.intType)} == 0) { BSQ_ABORT("Div by 0", "${filenameClean(this.currentFile)}", ${bop.sinfo.line}); }`;
                        const opp = `${this.varToCppName(bop.trgt)} = ${this.argToCpp(bop.lhs, this.typegen.intType)} / ${this.argToCpp(bop.rhs, this.typegen.intType)};`;

                        return chk + " " + opp;
                    }
                }
                else if (this.typegen.typecheckIsName(opt, /^NSCore::BigInt$/)) {
                    const bigop = new Map<string, string>().set("+", "add").set("-", "sub").set("*", "mult").set("/", "div").get(bop.op) as string;
                    const opp = `${this.varToCppName(bop.trgt)} = BSQBigInt::${bigop}(${this.argToCpp(bop.lhs, this.typegen.bigIntType)}, ${this.argToCpp(bop.rhs, this.typegen.bigIntType)});`;
                    if(bop.op !== "/") {
                        return opp;
                    }
                    else {
                        const chk = `if(${this.argToCpp(bop.rhs, this.typegen.bigIntType)}->eqI64(0)) { BSQ_ABORT("Div by 0", "${filenameClean(this.currentFile)}", ${bop.sinfo.line}); }`;
                        return chk + " " + opp;
                    }
                }
                else {
                    return `${this.varToCppName(bop.trgt)} = ${this.argToCpp(bop.lhs, this.typegen.float64Type)} ${bop.op} ${this.argToCpp(bop.rhs, this.typegen.float64Type)};`;
                }
            }
            case MIROpTag.MIRBinEq: {
                const beq = op as MIRBinEq;

                const lhvtypeinfer = this.typegen.getMIRType(beq.lhsInferType);
                const rhvtypeinfer = this.typegen.getMIRType(beq.rhsInferType);
                return `${this.varToCppName(beq.trgt)} = ${this.generateEquals(beq.op, lhvtypeinfer, beq.lhs, rhvtypeinfer, beq.rhs, !beq.relaxed)};`;
            }
            case MIROpTag.MIRBinLess: {
                const blt = op as MIRBinLess;

                const lhvtypeinfer = this.typegen.getMIRType(blt.lhsInferType);
                const rhvtypeinfer = this.typegen.getMIRType(blt.rhsInferType);
                return `${this.varToCppName(blt.trgt)} = ${this.generateLess(lhvtypeinfer, blt.lhs, rhvtypeinfer, blt.rhs, !blt.relaxed)};`;
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
                const infertype = this.typegen.getMIRType(top.argInferType);

                return `${this.varToCppName(top.trgt)} = ${this.generateTypeCheck(this.argToCpp(top.arg, argtype), argtype, infertype, oftype)};`;
            }
            case MIROpTag.MIRRegAssign: {
                const regop = op as MIRRegAssign;
                return `${this.varToCppName(regop.trgt)} = ${this.argToCpp(regop.src, this.getArgType(regop.trgt))};`;
            }
            case MIROpTag.MIRTruthyConvert: {
                const tcop = op as MIRTruthyConvert;
                return `${this.varToCppName(tcop.trgt)} = ${this.generateTruthyConvert(tcop.src)};`;
            }
            case MIROpTag.MIRVarStore: {
                const vsop = op as MIRVarStore;
                return `${this.varToCppName(vsop.name)} = ${this.argToCpp(vsop.src, this.getArgType(vsop.name))};`;
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
                    return `{ std::cout << diagnostic_format(${this.argToCpp(dbgop.value, this.typegen.anyType)}) << "\\n"; }`;
                }
            }
            case MIROpTag.MIRJump: {
                const jop = op as MIRJump;
                return `goto ${this.labelToCpp(jop.trgtblock)};`;
            }
            case MIROpTag.MIRJumpCond: {
                const cjop = op as MIRJumpCond;
                return `if(${this.argToCpp(cjop.arg, this.typegen.boolType)}) {goto ${this.labelToCpp(cjop.trueblock)};} else {goto ${cjop.falseblock};}`;
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
            const rctype = this.typegen.getRefCountableStatus(this.currentRType);
            if(rctype !== "no") {
                gblock.push(this.typegen.buildReturnOpForType(this.currentRType, "$$return", "$callerscope$") + ";");
            }
            
            gblock.push("return $$return;");
        }

        this.generatedBlocks.set(block.label, gblock);
    }

    generateCPPVarDecls(body: MIRBody, params: MIRFunctionParameter[]): string {
        const scopevar = this.varNameToCppName("$scope$");
        const refscope = `    BSQRefScope ${scopevar};`;

        let vdecls = new Map<string, string[]>();
        (body.vtypes as Map<string, string>).forEach((tkey, name) => {
            if (params.findIndex((p) => p.name === name) === -1) {
                const declt = this.typegen.getCPPReprFor(this.typegen.getMIRType(tkey)).std;
                if (!vdecls.has(declt)) {
                    vdecls.set(declt, [] as string[]);
                }

                (vdecls.get(declt) as string[]).push(this.varNameToCppName(name));
            }
        });
        let vdeclscpp: string[] = [];
        if (vdecls.has("BSQBool")) {
            vdeclscpp.push(`BSQBool ${(vdecls.get("BSQBool") as string[]).join(", ")};`);
        }
        if (vdecls.has("int64_t")) {
            vdeclscpp.push(`int64_t ${(vdecls.get("int64_t") as string[]).join(", ")};`);
        }
        [...vdecls].sort((a, b) => a[0].localeCompare(b[0])).forEach((kv) => {
            if (kv[0] !== "BSQBool" && kv[0] !== "int64_t") {
                vdeclscpp.push(kv[1].map((vname) => `${kv[0]} ${vname}`).join("; ") + ";");
            }
        });

        return [refscope, ...vdeclscpp].join("\n    ");
    }

    generateCPPInvoke(idecl: MIRInvokeDecl): { fwddecl: string, fulldecl: string } {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.getMIRType(idecl.resultType);

        const args = idecl.params.map((arg) => `${this.typegen.getCPPReprFor(this.typegen.getMIRType(arg.type)).std} ${this.varNameToCppName(arg.name)}`);
        const restype = this.typegen.getCPPReprFor(this.typegen.getMIRType(idecl.resultType)).std;

        if (this.typegen.getRefCountableStatus(this.typegen.getMIRType(idecl.resultType)) !== "no") {
                args.push(`BSQRefScope& $callerscope$`);
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

            const scopestrs = this.generateCPPVarDecls(idecl.body, idecl.params);

            return { fwddecl: decl + ";", fulldecl: `${decl}\n{\n${scopestrs}\n\n${blockstrs.join("\n\n")}\n}\n` };
        }
        else {
            assert(idecl instanceof MIRInvokePrimitiveDecl);

            const params = idecl.params.map((arg) => this.varNameToCppName(arg.name));
            return { fwddecl: decl + ";", fulldecl: `${decl} { ${this.generateBuiltinBody(idecl as MIRInvokePrimitiveDecl, params)} }\n` };
        }
    }

    getEnclosingListTypeForListOp(idecl: MIRInvokePrimitiveDecl): MIRType {
        return this.typegen.getMIRType(idecl.enclosingDecl as string);
    }

    getListContentsInfoForListOp(idecl: MIRInvokePrimitiveDecl): MIRType {
        return (this.typegen.assembly.entityDecls.get(idecl.enclosingDecl as string) as MIREntityTypeDecl).terms.get("T") as MIRType;
    }

    getListResultTypeFor(idecl: MIRInvokePrimitiveDecl): [string, string, string, string] {
        const le = this.typegen.assembly.entityDecls.get(idecl.resultType as string) as MIREntityTypeDecl;
        const ltype = this.typegen.getMIRType(le.tkey);
        const ctype = le.terms.get("T") as MIRType;
        const uinc = this.typegen.getFunctorsForType(ctype).inc;
        return [this.typegen.getCPPReprFor(ltype).base, this.typegen.getCPPReprFor(ctype).std, `MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(le.tkey)}`, uinc];
    }

    getSetContentsInfoForSetOp(idecl: MIRInvokePrimitiveDecl): MIRType {
        return (this.typegen.assembly.entityDecls.get(idecl.enclosingDecl as string) as MIREntityTypeDecl).terms.get("T") as MIRType;
    }

    getMapKeyContentsInfoForMapType(decl: MIRResolvedTypeKey): MIRType {
        return (this.typegen.assembly.entityDecls.get(decl) as MIREntityTypeDecl).terms.get("K") as MIRType;
    }

    getMapValueContentsInfoForMapType(decl: MIRResolvedTypeKey): MIRType {
        return (this.typegen.assembly.entityDecls.get(decl) as MIREntityTypeDecl).terms.get("V") as MIRType;
    }

    getMEntryTypeForMapType(decl: MIRResolvedTypeKey): string {
        const ktd = this.typegen.getCPPReprFor(this.getMapKeyContentsInfoForMapType(decl)).std;
        const vtd = this.typegen.getCPPReprFor(this.getMapValueContentsInfoForMapType(decl)).std;

        return `MEntry<${ktd}, ${vtd}>`;
    }

    getMEntryCmpTypeForMapType(decl: MIRResolvedTypeKey): string {
        const ktd = this.typegen.getCPPReprFor(this.getMapKeyContentsInfoForMapType(decl)).std;
        const kcmp = this.typegen.getFunctorsForType(this.getMapKeyContentsInfoForMapType(decl)).less;
        const vtd = this.typegen.getCPPReprFor(this.getMapValueContentsInfoForMapType(decl)).std;

        return `MEntryCMP<${ktd}, ${vtd}, ${kcmp}>`;
    }

    getEnclosingMapTypeForMapOp(idecl: MIRInvokePrimitiveDecl): MIRType {
        return this.typegen.getMIRType(idecl.enclosingDecl as string);
    }

    getMapKeyContentsInfoForMapOp(idecl: MIRInvokePrimitiveDecl): MIRType {
        return this.getMapKeyContentsInfoForMapType(idecl.enclosingDecl as string);
    }

    getMapValueContentsInfoForMapOp(idecl: MIRInvokePrimitiveDecl): MIRType {
        return this.getMapValueContentsInfoForMapType(idecl.enclosingDecl as string);
    }

    getMEntryTypeForMapOp(idecl: MIRInvokePrimitiveDecl): string {
        return this.getMEntryTypeForMapType(idecl.enclosingDecl as string);
    }

    getMEntryCmpTypeForMapOp(idecl: MIRInvokePrimitiveDecl): string {
        return this.getMEntryCmpTypeForMapType(idecl.enclosingDecl as string);
    }

    createListOpsFor(ltype: MIRType, ctype: MIRType): string {
        const lrepr = this.typegen.getCPPReprFor(ltype).base;
        const crepr = this.typegen.getCPPReprFor(ctype);
        const cops = this.typegen.getFunctorsForType(ctype);
        return `BSQListOps<${lrepr}, ${crepr.std}, ${cops.inc}, ${cops.dec}, ${cops.display}>`;
    }

    createMapOpsFor(mtype: MIRType, ktype: MIRType, vtype: MIRType): string {
        const mrepr = this.typegen.getCPPReprFor(mtype).base;
        const krepr = this.typegen.getCPPReprFor(ktype);
        const kops = this.typegen.getFunctorsForType(ktype);
        const vrepr = this.typegen.getCPPReprFor(vtype);
        const vops = this.typegen.getFunctorsForType(vtype);

        return `BSQMapOps<${mrepr}, ${krepr.std}, ${kops.dec}, ${kops.display}, ${kops.less}, ${kops.eq}, ${vrepr.std}, ${vops.dec}, ${vops.display}>`;
    }

    createPCodeInvokeForPred(pc: MIRPCode, arg: string): string {
        const cargs = pc.cargs.map((ca) => this.typegen.mangleStringForCpp(ca));
        return `${this.typegen.mangleStringForCpp(pc.code)}(${[arg, ...cargs].join(", ")})`;
    }

    generateBuiltinBody(idecl: MIRInvokePrimitiveDecl, params: string[]): string {
        const scopevar = this.varNameToCppName("$scope$");

        let bodystr = [];
        switch (idecl.implkey) {
            case "validator_accepts": {
                const rs = this.assembly.literalRegexs.get(this.assembly.validatorRegexs.get(idecl.enclosingDecl as MIRNominalTypeKey) as string) as MIRRegex;
                bodystr.push(compileRegexCppMatch(rs, params[0], "$$return"));
                break;
            }
            case "enum_create": {
                bodystr.push(`auto $$return = BSQEnum{ (uint32_t)${params[0]} };`);
                break;
            }
            case "float_min_value": {
                bodystr.push(`auto $$return = std::numeric_limits<double>::min();`);
                break;
            }
            case "float_max_value": {
                bodystr.push(`auto $$return = std::numeric_limits<double>::max();`);
                break;
            }
            case "float_infinity_value": {
                bodystr.push(`auto $$return = std::numeric_limits<double>::infinty();`);
                break;
            }
            case "float_nan_value": {
                bodystr.push(`auto $$return = std::numeric_limits<double>::quiet_NaN();`);
                break;
            }
            case "float64_isinfinity": {
                bodystr.push(`auto $$return = isinf(${params[0]});`);
                break;
            }
            case "float64_isnan": {
                bodystr.push(`auto $$return = isnan(${params[0]});`);
                break;
            }
            case "float64_compare": {
                const twc = `isless(${params[0]}, ${params[1]}) ? -1 : isless(${params[1]}, ${params[0]}) ? 1 : 0`
                bodystr.push(`BSQ_ASSERT(!isunordered(${params[0]}, ${params[1]}), "Cannot compare nan values"); auto $$return = ${twc};`);
                break;
            }
            case "float64_abs": {
                bodystr.push(`auto $$return = std::abs(${params[0]});`);
                break;
            }
            case "float64_ceiling": {
                bodystr.push(`auto $$return = ceil(${params[0]});`);
                break;
            }
            case "float64_floor": {
                bodystr.push(`auto $$return = floor(${params[0]});`);
                break;
            }
            case "float64_pow": {
                bodystr.push(`auto $$return = pow(${params[0]}, ${params[1]});`);
                break;
            }
            case "float64_pow2": {
                bodystr.push(`auto $$return = exp2(${params[0]});`);
                break;
            }
            case "float64_pow10": {
                bodystr.push(`auto $$return = pow(10.0, ${params[0]});`);
                break;
            }
            case "float64_exp": {
                bodystr.push(`auto $$return = exp(${params[0]});`);
                break;
            }
            case "float64_root": {
                bodystr.push(`auto $$return = ;`);
                break;
            }
            case "float64_square": {
                bodystr.push(`auto $$return = ${params[0]} * ${params[0]};`);
                break;
            }
            case "float64_sqrt": {
                bodystr.push(`auto $$return = sqrt(${params[0]});`);
                break;
            }
            case "float64_log": {
                bodystr.push(`auto $$return = log(${params[0]});`);
                break;
            }
            case "float64_log2": {
                bodystr.push(`auto $$return = log2(${params[0]});`);
                break;
            }
            case "float64_log10": {
                bodystr.push(`auto $$return = log10(${params[0]});`);
                break;
            }
            case "float64_sin": {
                bodystr.push(`auto $$return = sin(${params[0]});`);
                break;
            }
            case "float64_cos": {
                bodystr.push(`auto $$return = cos(${params[0]});`);
                break;
            }
            case "float64_tan": {
                bodystr.push(`auto $$return = tan(${params[0]});`);
                break;
            }
            case "float64_min": {
                bodystr.push(`auto $$return = fmin(${params[0]}, ${params[1]});`);
                break;
            }
            case "float64_max": {
                bodystr.push(`auto $$return = fmax(${params[0]}, ${params[1]});`);
                break;
            }
            case "float64_sum": {
                bodystr.push(`auto $$return = std::reduce(${CPP_EXECUTION_POLICY}, ${params[0]}->entries.begin(), ${params[0]}->entries.end(), 0.0);`);
                break;
            }
            case "float64_product": {
                bodystr.push(`auto $$return = std::reduce(${CPP_EXECUTION_POLICY}, ${params[0]}->entries.begin(), ${params[0]}->entries.end(), 1.0, [](double a, double b) { return a * b; });`);
                break;
            }
            case "idkey_from_simple": {
                const rrepr = this.typegen.getCPPReprFor(this.currentRType);
                bodystr.push(`auto $$return = ${rrepr.basetype}{ ${params[0]} };`);
                break;
            }
            case "idkey_from_composite": {
                const rrepr = this.typegen.getCPPReprFor(this.currentRType);
                bodystr.push(`auto $$return = ${rrepr.basetype}{ ${params.join(", ")} };`);
                break;
            }
            case "string_count": {
                bodystr.push(`auto $$return = ${params[0]}->count();`);
                break;
            }
            case "string_charat": {
                bodystr.push(`BSQString $$return = { nullptr };`);
                bodystr.push(`${params[0]}->charat(${params[1]}, $$return);`);
                break;
            }
            case "string_concat": {
                bodystr.push(`BSQString $$return = { nullptr };`);
                bodystr.push(`${params[0]}->concat(${params[1]}, $$return);`);
                break;
            }
            case "string_substring": {
                bodystr.push(`BSQString $$return = { nullptr };`)
                bodystr.push(`${params[0]}->concat(${params[1]}, ${params[2]}, $$return);`);
            }
            case "safestring_string": {
                bodystr.push(`auto $$return = ${params[0]};`);
                break;
            }
            case "safestring_unsafe_from": {
                bodystr.push(`auto $$return = ${params[0]};`);
                break;
            }
            case "stringof_string": {
                bodystr.push(`auto $$return = ${params[0]};`);
                break;
            }
            case "stringof_unsafe_from": {
                bodystr.push(`auto $$return = ${params[0]};`);
                break;
            }
            case "list_zip": {
                const ltype1 = this.typegen.getMIRType(idecl.params[0].type);
                const l1contents = (this.typegen.assembly.entityDecls.get(ltype1.trkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
                const ltype1repr = this.typegen.getCPPReprFor(ltype1);
            
                const ltype2 = this.typegen.getMIRType(idecl.params[1].type);
                const l2contents = (this.typegen.assembly.entityDecls.get(ltype2.trkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
                const ltype2repr = this.typegen.getCPPReprFor(ltype2);

                const rtype = this.typegen.getMIRType(idecl.resultType);
                const rcontents = (this.typegen.assembly.entityDecls.get(rtype.trkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
                const rtyperepr = this.typegen.getCPPReprFor(rtype);
                
                //TODO: it would be nice if we had specialized versions of these that didn't dump into our scope manager
                const iflag = this.typegen.generateInitialDataKindFlag(rcontents);
                const codecc1 = this.typegen.coerce("uu", l1contents, this.typegen.anyType);
                const codecc2 = this.typegen.coerce("vv", l2contents, this.typegen.anyType);
                const zlambda = `[&${scopevar}](${this.typegen.getCPPReprFor(l1contents).std} uu, ${this.typegen.getCPPReprFor(l2contents).std} vv) -> ${this.typegen.getCPPReprFor(rcontents).std} { return BSQTuple::createFromSingle<${iflag}>({ INC_REF_CHECK(Value, ${codecc1}), INC_REF_CHECK(Value, ${codecc2}) }); }`;

                bodystr = `auto $$return = BSQListUtilOps::list_zip<${ltype1repr.base}, ${ltype2repr.base}, ${rtyperepr.base}, ${this.typegen.getCPPReprFor(rcontents).std}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(rtype.trkey)}>(${params[0]}, ${params[1]}, ${zlambda});`;
                break;
            }
            case "list_unzip": {
                const rtype = this.typegen.getMIRType(idecl.resultType);
                const [rt1, rt2] = (rtype.options[0] as MIREphemeralListType).entries;
                const rtyperepr = this.typegen.getCPPReprFor(rtype);

                const repr1 = this.typegen.getCPPReprFor(rt1);
                const contents1 = (this.typegen.assembly.entityDecls.get(rt1.trkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
                const contents1repr = this.typegen.getCPPReprFor(contents1);
                const repr2 = this.typegen.getCPPReprFor(rt2);
                const contents2 = (this.typegen.assembly.entityDecls.get(rt2.trkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
                const contents2repr = this.typegen.getCPPReprFor(contents2);

                const ltype = this.typegen.getMIRType(idecl.params[0].type);
                const ltyperepr = this.typegen.getCPPReprFor(ltype);
                const lcontents = (this.typegen.assembly.entityDecls.get(ltype.trkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
                const lcontentsrepr = this.typegen.getCPPReprFor(lcontents);

                //TODO: it would be nice if we had specialized versions of these that didn't dump into our scope manager
                const acc1 = this.typegen.coerce("cr.atFixed<0>()", this.typegen.anyType, contents1);
                const acc2 = this.typegen.coerce("cr.atFixed<1>()", this.typegen.anyType, contents2);

                const uzlambda = `[](${lcontentsrepr.std} cr) -> std::pair<${contents1repr.std}, ${contents2repr.std}> { return std::make_pair(${acc1}, ${acc2}); }`;
                const rv = `auto $uvpair$ = BSQListUtilOps::list_unzip<${repr1.base}, ${contents1repr.std}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(rt1.trkey)}, ${repr2.base}, ${contents2repr.std}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(rt2.trkey)}, ${ltyperepr.base}>(${params[0]}, ${uzlambda});`;

                bodystr = `${rv} auto $$return = ${rtyperepr.base}{$uvpair$.first, $uvpair$.second};`;
                break;
            }
            case "list_range": {
                const rtype = this.typegen.getMIRType(idecl.resultType);
                const rtyperepr = this.typegen.getCPPReprFor(rtype);

                bodystr = `auto $$return = BSQListUtilOps::list_range<${rtyperepr.base}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(rtype.trkey)}>(${params[0]}, ${params[1]});`;
                break;
            }
            case "list_size": {
                bodystr.push(`auto $$return = (int64_t)${params[0]}->count;`);
                break;
            }
            case "list_unsafe_get": {
                bodystr.push(`auto $$return = ${params[0]}->at(${params[1]});`);
                break;
            }
            case "list_concat": {
                const lrepr = this.typegen.getCPPReprFor(this.getEnclosingListTypeForListOp(idecl));
                const argrepr = this.typegen.getCPPReprFor(this.typegen.getMIRType(idecl.params[0].type));

                bodystr.push(`auto $$return = ${lrepr.basetype}::list_concat<${lrepr.basetype}, ${argrepr.storagetype}>(${params[0]}, META_DATA_LOAD_DECL(${lrepr.metadataName}));`)
                break;
            }
            case "list_fill": {
                const lrepr = this.typegen.getCPPReprFor(this.getEnclosingListTypeForListOp(idecl));
                const crepr = this.typegen.getCPPReprFor(this.getListContentsInfoForListOp(idecl));
                
                bodystr.push(`${crepr.storagetype} contents = nullptr;`);
                bodystr.push(`auto $$return = Allocator::GlobalAllocator.allocateTPlus<${lrepr.basetype}, ${crepr.storagetype}>(META_DATA_LOAD_DECL(${lrepr.metadataName}), ${params[0]}, &contents);`);
                bodystr.push(`$$return->count = ${params[0]};`)
                bodystr.push(`std::fill(contents, contents + ${params[0]}, ${params[1]});`);
                break;
            }
            case "list_toset": {
                const settype = this.typegen.getMIRType(idecl.resultType);
                const setrepr = this.typegen.getCPPReprFor(settype);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const crepr = this.typegen.getCPPReprFor(ctype);
                const cfuncs = this.typegen.getFunctorsForType(ctype);

                const ntype = `MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(settype.trkey)}`;
                const stemplate = `BSQSet<${crepr.std}, ${cfuncs.dec}, ${cfuncs.display}, ${cfuncs.less}, ${cfuncs.eq}>`;
                bodystr = `auto $$return =  BSQ_NEW_NO_RC(${setrepr.base}, ${ntype}, ${stemplate}::processSingletonSetInit<${cfuncs.inc}>(${params[0]}->entries));`;
                break;
            }
            case "list_all": {
                const pci = this.createPCodeInvokeForPred(idecl.pcodes.get("p") as MIRPCode, `${params[0]}->at(i)`);
                bodystr.push(`auto $$return = true;`);
                bodystr.push(`for(size_t i = 0; i < ${params[0]}->count; ++i) { if(!${pci}) { $$return = false; break; } }`);
                break;
            }
            case "list_any": {
                const pci = this.createPCodeInvokeForPred(idecl.pcodes.get("p") as MIRPCode, `${params[0]}->at(i)`);
                bodystr.push(`auto $$return = false;`);
                bodystr.push(`for(size_t i = 0; i < ${params[0]}->count; ++i) { if(${pci}) { $$return = true; break; } }`);
                break;
            }
            case "list_none": {
                const pci = this.createPCodeInvokeForPred(idecl.pcodes.get("p") as MIRPCode, `${params[0]}->at(i)`);
                bodystr.push(`auto $$return = true;`);
                bodystr.push(`for(size_t i = 0; i < ${params[0]}->count; ++i) { if(${pci}) { $$return = false; break; } }`);
                break;
            }
            case "list_count": {
                const pci = this.createPCodeInvokeForPred(idecl.pcodes.get("p") as MIRPCode, `${params[0]}->at(i)`);
                bodystr.push(`auto $$return = 0;`);
                bodystr.push(`for(size_t i = 0; i < ${params[0]}->count; ++i) { if(${pci}) { $$return++; } }`);
                break;
            }
            case "list_countnot": {
                const pci = this.createPCodeInvokeForPred(idecl.pcodes.get("p") as MIRPCode, `${params[0]}->at(i)`);
                bodystr.push(`auto $$return = 0;`);
                bodystr.push(`for(size_t i = 0; i < ${params[0]}->count; ++i) { if(!${pci}) { $$return++; } }`);
                break;
            }
            case "list_indexof": {
                const pci = this.createPCodeInvokeForPred(idecl.pcodes.get("p") as MIRPCode, `${params[0]}->at(i)`);
                bodystr.push(`auto $$return = ${params[2]};`);
                bodystr.push(`for(size_t i = ${params[1]}; i < ${params[2]}; ++i) { if(${pci}) { $$return = i; break; } }`);
                break;
            }
            case "list_indexoflast": {
                const pci = this.createPCodeInvokeForPred(idecl.pcodes.get("p") as MIRPCode, `${params[0]}->at(i)`);
                bodystr.push(`auto $$return = ${params[2]};`);
                bodystr.push(`for(int64_t i = ${params[2]}; i > ${params[1]}; --i) { if(${pci}) { $$return = i; break; } }`);
                break;
            }
            case "list_indexofnot": {
                const pci = this.createPCodeInvokeForPred(idecl.pcodes.get("p") as MIRPCode, `${params[0]}->at(i)`);
                bodystr.push(`auto $$return = ${params[2]};`);
                bodystr.push(`for(size_t i = ${params[1]}; i < ${params[2]}; ++i) { if(!${pci}) { $$return = i; break; } }`);
                break;
            }
            case "list_indexoflastnot": {
                const pci = this.createPCodeInvokeForPred(idecl.pcodes.get("p") as MIRPCode, `${params[0]}->at(i)`);
                bodystr.push(`auto $$return = ${params[2]};`);
                bodystr.push(`for(int64_t i = ${params[2]}; i > ${params[1]}; --i) { if(!${pci}) { $$return = i; break; } }`);
                break;
            }
            case "list_count_keytype": {
                const crepr = this.typegen.getCPPReprFor(this.getListContentsInfoForListOp(idecl));
                const eqf = this.typegen.getFunctorsForType(this.getListContentsInfoForListOp(idecl)).eq;
                const lambda = `[${params[1]}](${crepr.storagetype} a) { return ${eqf}{}(a, ${params[1]}); }`
                bodystr.push(`auto $$return = std::count_if(${CPP_EXECUTION_POLICY}, ${params[0]}->begin(), ${params[0]}->end(), ${lambda});`);
                break;
            }
            case "list_indexof_keytype": {
                const eqf = this.typegen.getFunctorsForType(this.getListContentsInfoForListOp(idecl)).eq;
                bodystr.push(`auto $$return = ${params[2]};`);
                bodystr.push(`for(size_t i = ${params[1]}; i < ${params[2]}; ++i) { if(${eqf}{}(${params[3]}, ${params[0]}->at(i))) { $$return = i; break; } }`);
                break;
            }
            case "list_indexoflast_keytype": {
                const eqf = this.typegen.getFunctorsForType(this.getListContentsInfoForListOp(idecl)).eq;
                bodystr.push(`auto $$return = ${params[2]};`);
                bodystr.push(`for(int64_t i = ${params[2]}; i > ${params[1]}; --i) { if(${eqf}{}(${params[3]}, ${params[0]}->at(i))) { $$return = i; break; } }`);
                break;
            }
            case "list_min": {
                const lessf = this.typegen.getFunctorsForType(this.getListContentsInfoForListOp(idecl)).less;
                bodystr.push(`auto $$return = *std::min_element(${CPP_EXECUTION_POLICY}, ${params[0]}->begin(), ${params[0]}->end(), ${lessf}{});`);
                break;
            }
            case "list_max": {
                const lessf = this.typegen.getFunctorsForType(this.getListContentsInfoForListOp(idecl)).less;
                bodystr.push(`auto $$return = *std::max_element(${CPP_EXECUTION_POLICY}, ${params[0]}->begin(), ${params[0]}->end(), ${lessf}{});`);
                break;
            }
            case "list_sum": {
                const ctype = this.getListContentsInfoForListOp(idecl);
                if(ctype.trkey === "NSCore::Int") {
                    bodystr.push(`auto $$return = ${params[0]}->list_sum_int<${CPP_EXECUTION_POLICY}>();`);
                }
                else if(ctype.trkey === "NSCore::BigInt") {
                    bodystr.push(`auto $$return = ${params[0]}->list_sum_bigint<${CPP_EXECUTION_POLICY}>();`);
                }
                else {
                    bodystr.push(`auto $$return = ${params[0]}->list_sum_mixed<${CPP_EXECUTION_POLICY}>();`);
                }
                break;
            }
            case "list_sort": {
                //We need to do a custom sort here that always loads from the home location in case we trigger a GC in the cmp function
                assert("NOT IMPLEMENTED sort");
                break;
            }
            case "list_filter": {
                const lrepr = this.typegen.getCPPReprFor(this.getEnclosingListTypeForListOp(idecl));
                const crepr = this.typegen.getCPPReprFor(this.getListContentsInfoForListOp(idecl));
                const pci = this.createPCodeInvokeForPred(idecl.pcodes.get("p") as MIRPCode, `${params[0]}->at(i)`);

                bodystr.push(`auto tmp = Allocator::GlobalAllocator.allocateTPlus<${lrepr.basetype}, ${crepr.storagetype}>(META_DATA_LOAD_DECL(${lrepr.metadataName}), ${params[0]}->count, nullptr);`);
                bodystr.push(`Allocator::GlobalAllocator.pushRoot(tmp);`);
                bodystr.push(`lcount = ${params[0]}->count;`);
                bodystr.push(`for(size_t i = 0; i < lcount; ++i) { if(${pci}) { tmp->copyto(tmp->count++, ${params[0]}, i); } }`);
                bodystr.push(`$$return = Allocator::GlobalAllocator.shrink(Allocator::GlobalAllocator.popRoot<${lrepr.basetype}>(), ${lrepr.alignedSize}, ${crepr.alignedSize}, ${params[0]}->count, tmp->count);`);
                break;
            }
            case "list_filternot": {
                const lrepr = this.typegen.getCPPReprFor(this.getEnclosingListTypeForListOp(idecl));
                const crepr = this.typegen.getCPPReprFor(this.getListContentsInfoForListOp(idecl));
                const pci = this.createPCodeInvokeForPred(idecl.pcodes.get("p") as MIRPCode, `${params[0]}->at(i)`);

                bodystr.push(`auto tmp = Allocator::GlobalAllocator.allocateTPlus<${lrepr.basetype}, ${crepr.storagetype}>(META_DATA_LOAD_DECL(${lrepr.metadataName}), ${params[0]}->count, nullptr);`);
                bodystr.push(`Allocator::GlobalAllocator.pushRoot(tmp);`);
                bodystr.push(`lcount = ${params[0]}->count;`);
                bodystr.push(`for(size_t i = 0; i < lcount; ++i) { if(!${pci}) { tmp->copyto(tmp->count++, ${params[0]}, i); } }`);
                bodystr.push(`$$return = Allocator::GlobalAllocator.shrink(Allocator::GlobalAllocator.popRoot<${lrepr.basetype}>(), ${lrepr.alignedSize}, ${crepr.alignedSize}, ${params[0]}->count, tmp->count);`);
                break;
            }
            case "list_oftype": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const rltype = this.typegen.getMIRType(idecl.resultType);
                const rlctype = (this.typegen.assembly.entityDecls.get(rltype.trkey) as MIREntityTypeDecl).terms.get("T") as MIRType;

                const codetc = this.generateTypeCheck(`${params[0]}->at(i)`, ctype, ctype, rlctype);
                if(codetc === "false") {
                    bodystr.push(`auto $$return = ${this.typegen.getCPPReprFor(ltype).basetype}::empty;`);
                }
                else {
                    const rlrepr = this.typegen.getCPPReprFor(rltype);
                    const rlcrepr = this.typegen.getCPPReprFor(rlctype);
                    const codecc = this.coerceAccessInline([`${params[0]}->at(i)`, ctype, rlctype]);
                    const codeccv = `${rlrepr.storagetype}& ccv = ${codecc[1][0]};`;

                    bodystr.push(`auto tmp = Allocator::GlobalAllocator.allocateTPlus<${rlrepr.basetype}, ${rlcrepr.storagetype}>(META_DATA_LOAD_DECL(${rlrepr.metadataName}), ${params[0]}->count, nullptr);`);
                    bodystr.push(`Allocator::GlobalAllocator.pushRoot(tmp);`);
                    bodystr.push(`lcount = ${params[0]}->count;`);
                    bodystr.push(`for(size_t i = 0; i < lcount; ++i) { if(${codetc}) { ${[...codecc[0], codeccv].join(" ")} tmp->store(tmp->count++, ccv); } }`);
                    bodystr.push(`$$return = Allocator::GlobalAllocator.shrink(Allocator::GlobalAllocator.popRoot<${rlrepr.basetype}>(), ${rlrepr.alignedSize}, ${rlcrepr.alignedSize}, ${params[0]}->count, tmp->count);`);
                }
                break;
            }
            case "list_cast": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const rltype = this.typegen.getMIRType(idecl.resultType);
                const rlctype = (this.typegen.assembly.entityDecls.get(rltype.trkey) as MIREntityTypeDecl).terms.get("T") as MIRType;

                const codetc = this.generateTypeCheck(`${params[0]}->at(i)`, ctype, ctype, rlctype);
                if(codetc === "false") {
                    const abrt = `BSQ_ABORT("Invalid element to cast", "${filenameClean(this.currentFile)}", ${idecl.sourceLocation.line});`;
                    const iec = `if(${params[0]}->entries.size() != 0) { ${abrt} }`;
                    bodystr.push(`${iec} auto $$return = ${this.typegen.getCPPReprFor(ltype).basetype}::empty;`);
                }
                else {
                    const rlrepr = this.typegen.getCPPReprFor(rltype);
                    const rlcrepr = this.typegen.getCPPReprFor(rlctype);
                    const codecc = this.coerceAccessInline([`${params[0]}->at(i)`, ctype, rlctype]);
                    const codeccv = `${rlrepr.storagetype}& ccv = ${codecc[1][0]};`;

                    bodystr.push(`auto tmp = Allocator::GlobalAllocator.allocateTPlus<${rlrepr.basetype}, ${rlcrepr.storagetype}>(META_DATA_LOAD_DECL(${rlrepr.metadataName}), ${params[0]}->count, nullptr);`);
                    bodystr.push(`Allocator::GlobalAllocator.pushRoot(tmp);`);
                    bodystr.push(`lcount = ${params[0]}->count;`);
                    bodystr.push(`for(size_t i = 0; i < lcount; ++i) { BSQ_ASSERT(${codetc}); ${[...codecc[0], codeccv].join(" ")} tmp->store(tmp->count++, ccv); }`);
                    bodystr.push(`$$return = Allocator::GlobalAllocator.popRoot<${rlrepr.basetype}>();`);
                }
                break;
            }
            case "list_slice": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);

                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_slice(${params[0]}, ${params[1]}, ${params[2]});`;
                break;
            }
            case "list_takewhile": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const lambda = this.createLambdaFor(idecl.pcodes.get("p") as MIRPCode);
                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_takewhile(${params[0]}, ${lambda});`;
                break;
            }
            case "list_discardwhile": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const lambda = this.createLambdaFor(idecl.pcodes.get("p") as MIRPCode);
                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_discardwhile(${params[0]}, ${lambda});`;
                break;
            }
            case "list_takeuntil": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const lambda = this.createLambdaFor(idecl.pcodes.get("p") as MIRPCode);
                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_takeuntil(${params[0]}, ${lambda});`;
                break;
            }
            case "list_discarduntil": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const lambda = this.createLambdaFor(idecl.pcodes.get("p") as MIRPCode);
                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_discarduntil(${params[0]}, ${lambda});`;
                break;
            }
            case "list_unique": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const cmp = this.typegen.getFunctorsForType(ctype).less;
                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_unique<${cmp}>(${params[0]});`;
                break;
            }
            case "list_reverse": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_reverse(${params[0]});`;
                break;
            }
            case "list_map": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const [utype, ucontents, utag] = this.getListResultTypeFor(idecl);

                const lambdascope = this.typegen.mangleStringForCpp("$lambda_scope$");
                const lambda = this.createLambdaFor(idecl.pcodes.get("f") as MIRPCode, lambdascope);
                bodystr = `BSQRefScope ${lambdascope}(true); auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_map<${utype}, ${ucontents}, ${utag}>(${params[0]}, ${lambda});`;
                break;
            }
            case "list_mapindex": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const [utype, ucontents, utag] = this.getListResultTypeFor(idecl);

                const lambdascope = this.typegen.mangleStringForCpp("$lambda_scope$");
                const lambda = this.createLambdaFor(idecl.pcodes.get("f") as MIRPCode, lambdascope);
                bodystr = `BSQRefScope ${lambdascope}(true); auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_mapindex<${utype}, ${ucontents}, ${utag}>(${params[0]}, ${lambda});`;
                break;
            }
            case "list_project": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const [utype, ucontents, utag, incu] = this.getListResultTypeFor(idecl);
                const mapt = this.typegen.getCPPReprFor(this.typegen.getMIRType(idecl.params[1].type)).base;

                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_project<${utype}, ${ucontents}, ${utag}, ${mapt}, ${incu}>(${params[0]}, ${params[1]});`;
                break;
            }
            case "list_tryproject": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const [utype, ucontents, utag, incu] = this.getListResultTypeFor(idecl);
                const mapt = this.typegen.getCPPReprFor(this.typegen.getMIRType(idecl.params[1].type)).base;

                const mirutype = (this.typegen.assembly.entityDecls.get(this.typegen.getMIRType(idecl.resultType).trkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
                const utyperepr = this.typegen.getCPPReprFor(mirutype);

                const mirvvtype = (this.typegen.assembly.entityDecls.get(this.typegen.getMIRType(idecl.params[1].type).trkey) as MIREntityTypeDecl).terms.get("V") as MIRType;
                const vvtyperepr = this.typegen.getCPPReprFor(mirvvtype);

                //TODO: it would be nice if we had specialized versions of these that didn't dump into our scope manager
                const codecc = this.typegen.coerce("ccv", mirvvtype, mirutype);
                const lambdacc = `[&${scopevar}](${this.typegen.getCPPReprFor(ctype).std} ccv) -> ${utyperepr.std} { return ${codecc}; }`;
                const unone = this.typegen.coerce("BSQ_VALUE_NONE", this.typegen.noneType, mirutype);

                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_tryproject<${utype}, ${ucontents}, ${vvtyperepr.std}, ${utag}, ${mapt}, ${incu}>(${params[0]}, ${params[1]}, ${unone}, ${lambdacc});`;
                break;
            }
            case "list_defaultproject": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const [utype, ucontents, utag, incu] = this.getListResultTypeFor(idecl);
                const mapt = this.typegen.getCPPReprFor(this.typegen.getMIRType(idecl.params[1].type)).base;

                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_defaultproject<${utype}, ${ucontents}, ${utag}, ${mapt}, ${incu}>(${params[0]}, ${params[1]}, ${params[2]});`;
                break;
            }
            case "list_zipindex": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const [utype, ucontents, utag] = this.getListResultTypeFor(idecl);
            
                //TODO: it would be nice if we had specialized versions of these that didn't dump into our scope manager
                const codecc = this.typegen.coerce("u", ctype, this.typegen.anyType);
                const crepr = this.typegen.getCPPReprFor(ctype);
                const iflag = this.typegen.generateInitialDataKindFlag(ctype); //int component goes along with everything so just ignore it
                const lambda = `[&${scopevar}](int64_t i, ${crepr.std} u) -> ${ucontents} { return BSQTuple::createFromSingle<${iflag}>({ BSQ_ENCODE_VALUE_TAGGED_INT(i), INC_REF_CHECK(Value, ${codecc}) }); }`;

                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_zipindex<${utype}, ${ucontents}, ${utag}>(${params[0]}, ${lambda});`;
                break;
            }
            case "list_join": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const utype = this.typegen.getMIRType(idecl.params[1].type);
                const ucontents = (this.typegen.assembly.entityDecls.get(utype.trkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
                const [tutype, tucontents, tutag] = this.getListResultTypeFor(idecl);
            
                //TODO: it would be nice if we had specialized versions of these that didn't dump into our scope manager
                const codecc = this.typegen.coerce("v", ctype, this.typegen.anyType);
                const codecu = this.typegen.coerce("u", ucontents, this.typegen.anyType);
                const crepr = this.typegen.getCPPReprFor(ctype);
                const urepr = this.typegen.getCPPReprFor(ucontents);
                const iflag = `${this.typegen.generateInitialDataKindFlag(ctype)} & ${this.typegen.generateInitialDataKindFlag(ucontents)}`;
                const lambda = `[&${scopevar}](${crepr.std} v, ${urepr.std} u) -> ${tucontents} { return BSQTuple::createFromSingle<${iflag}>({ INC_REF_CHECK(Value, ${codecc}), INC_REF_CHECK(Value, ${codecu}) }); }`;

                const lambdap = this.createLambdaFor(idecl.pcodes.get("p") as MIRPCode);

                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_join<${tutype}, ${tucontents}, ${this.typegen.getCPPReprFor(utype).base}, ${urepr.std}, ${tutag}>(${params[0]}, ${params[1]}, ${lambda}, ${lambdap});`;
                break;
            }
            case "list_joingroup": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                const utype = this.typegen.getMIRType(idecl.params[1].type);
                const ucontents = (this.typegen.assembly.entityDecls.get(utype.trkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
                const [tutype, tucontents, tutag] = this.getListResultTypeFor(idecl);
            
                //TODO: it would be nice if we had specialized versions of these that didn't dump into our scope manager
                const codecc = this.typegen.coerce("v", ctype, this.typegen.anyType);
                const codecu = this.typegen.coerce("u", utype, this.typegen.anyType);
                const crepr = this.typegen.getCPPReprFor(ctype);
                const urepr = this.typegen.getCPPReprFor(utype);
                const iflag = `${this.typegen.generateInitialDataKindFlag(ctype)} & ${this.typegen.generateInitialDataKindFlag(ucontents)}`;
                const lambda = `[&${scopevar}](${crepr.std} v, ${urepr.std} u) -> ${tucontents} { return BSQTuple::createFromSingle<${iflag}>({ INC_REF_CHECK(Value, ${codecc}), INC_REF_CHECK(Value, ${codecu}) }); }`;

                const lambdap = this.createLambdaFor(idecl.pcodes.get("p") as MIRPCode);

                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_joingroup<${tutype}, ${tucontents}, ${this.typegen.getCPPReprFor(utype).base}, ${this.typegen.getCPPReprFor(ucontents).std}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(utype.trkey)}, ${tutag}, ${this.typegen.getFunctorsForType(ucontents).inc}>(${params[0]}, ${params[1]}, ${lambda}, ${lambdap});`;
                break;
            }

            case "list_append": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
                
                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_append(${params[0]}, ${params[1]});`;
                break;
            }
            case "list_partition": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);
            
                const maptype = this.typegen.getMIRType(idecl.resultType);
                const mapentrytype = this.getMEntryTypeForMapType(maptype.trkey);
                const ktype = this.getMapKeyContentsInfoForMapType(maptype.trkey);
                const krepr = this.typegen.getCPPReprFor(ktype);
                const kops = this.typegen.getFunctorsForType(ktype);

                const lambdascope = this.typegen.mangleStringForCpp("$lambda_scope$");
                const lambdapf = this.createLambdaFor(idecl.pcodes.get("pf") as MIRPCode, lambdascope);
                const lambdamec = `[](${this.typegen.getCPPReprFor(ktype).std} kk, ${this.typegen.getCPPReprFor(ltype).std} ll) -> ${mapentrytype} { return ${mapentrytype}{kk, ll}; }`;

                bodystr = `BSQRefScope ${lambdascope}(true); auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_partition<${this.typegen.getCPPReprFor(maptype).base}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(maptype.trkey)}, ${mapentrytype}, ${krepr.std}, ${kops.dec}, ${kops.less}>(${params[0]}, ${lambdapf}, ${lambdamec});`
                break;
            }
            case "list_toindexmap": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);

                const maptype = this.typegen.getMIRType(idecl.resultType);
                const maptyperepr = this.typegen.getCPPReprFor(maptype);
                const mapentrytype = this.getMEntryTypeForMapType(maptype.trkey);

                const lambdamec = `[](int64_t kk, ${this.typegen.getCPPReprFor(ctype).std} vv) -> ${mapentrytype} { return ${mapentrytype}{kk, ${this.typegen.getFunctorsForType(ctype).inc}{}(vv)}; }`;

                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_toindexmap<${maptyperepr.base}, ${mapentrytype}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(maptype.trkey)}>(${params[0]}, ${lambdamec});`;
                break;
            }
            case "list_transformindexmap": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);

                const maptype = this.typegen.getMIRType(idecl.resultType);
                const vftype = this.getMapValueContentsInfoForMapType(idecl.resultType)
                const maptyperepr = this.typegen.getCPPReprFor(maptype);
                const mapentrytype = this.getMEntryTypeForMapType(maptype.trkey);

                const lambdascope = this.typegen.mangleStringForCpp("$lambda_scope$");
                const lambdavf = this.createLambdaFor(idecl.pcodes.get("vf") as MIRPCode, lambdascope);
                const lambdamec = `[](int64_t kk, ${this.typegen.getCPPReprFor(vftype).std} vv) -> ${mapentrytype} { return ${mapentrytype}{kk, vv}; }`;

                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_transformindexmap<${maptyperepr.base}, ${mapentrytype}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(maptype.trkey)}>(${params[0]}, ${lambdavf}, ${lambdamec});`;
                break;
            }
            case "list_transformmap": {
                const ltype = this.getEnclosingListTypeForListOp(idecl);
                const ctype = this.getListContentsInfoForListOp(idecl);

                const maptype = this.typegen.getMIRType(idecl.resultType);
                const kftype = this.getMapKeyContentsInfoForMapType(idecl.resultType)
                const vftype = this.getMapValueContentsInfoForMapType(idecl.resultType)
                const maptyperepr = this.typegen.getCPPReprFor(maptype);
                const mapentrytype = this.getMEntryTypeForMapType(maptype.trkey);

                const lambdascope = this.typegen.mangleStringForCpp("$lambda_scope$");
                const lambdakf = this.createLambdaFor(idecl.pcodes.get("kf") as MIRPCode, lambdascope);
                const lambdavf = this.createLambdaFor(idecl.pcodes.get("vf") as MIRPCode, lambdascope);
                const lambdamec = `[](${this.typegen.getCPPReprFor(kftype).std} kk, ${this.typegen.getCPPReprFor(vftype).std} vv) -> ${mapentrytype} { return ${mapentrytype}{kk, vv}; }`;

                bodystr = `auto $$return = ${this.createListOpsFor(ltype, ctype)}::list_transformmap<${maptyperepr.base}, ${mapentrytype}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(maptype.trkey)}, ${this.typegen.getCPPReprFor(kftype).std}, ${this.typegen.getFunctorsForType(kftype).less}, ${this.typegen.getCPPReprFor(vftype).std}>(${params[0]}, ${lambdakf}, ${lambdavf}, ${lambdamec});`;
                break;
            }
            case "set_size": {
                bodystr = `auto $$return = ${params[0]}->entries.size();`;
                break;
            }
            case "set_has_key": {
                const tcmp = this.typegen.getFunctorsForType(this.getSetContentsInfoForSetOp(idecl)).less;
                bodystr = `auto $$return = std::binary_search(${params[0]}->entries.begin(), ${params[0]}->entries.end(), ${params[1]}, ${tcmp}{});`;
                break;
            }
            case "map_size": {
                bodystr = `auto $$return = ${params[0]}->entries.size();`;
                break;
            }
            case "map_has_key": {
                bodystr = `auto $$return = ${params[0]}->hasKey(${params[1]});`;
                break;
            }
            case "map_at_val": {
                bodystr = `auto $$return = ${params[0]}->getValue(${params[1]});`;
                break;
            }
            case "map_key_list": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);
                const ltype = this.typegen.getMIRType(idecl.resultType);
                const ltyperepr = this.typegen.getCPPReprFor(ltype).base;

                bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_key_list<${ltyperepr}, ${this.typegen.getFunctorsForType(ktype).inc}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(ltype.trkey)}>(${params[0]});`;
                break;
            }
            case "map_key_set": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);
                const stype = this.typegen.getMIRType(idecl.resultType);
                const styperepr = this.typegen.getCPPReprFor(stype).base;

                bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_key_set<${styperepr}, ${this.typegen.getFunctorsForType(ktype).inc}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(stype.trkey)}>(${params[0]});`;
                break;
            }
            case "map_values": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);
                const ltype = this.typegen.getMIRType(idecl.resultType);
                const ltyperepr = this.typegen.getCPPReprFor(ltype).base;

                bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_values<${ltyperepr}, ${this.typegen.getFunctorsForType(vtype).inc}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(ltype.trkey)}>(${params[0]});`;
                break;
            }
            case "map_entries": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);
                const ltype = this.typegen.getMIRType(idecl.resultType);
                const ltyperepr = this.typegen.getCPPReprFor(ltype).base;

                const etype = (this.typegen.assembly.entityDecls.get(ltype.trkey) as MIREntityTypeDecl).terms.get("T") as MIRType;
                const etyperepr = this.typegen.getCPPReprFor(etype);

                const lambdamec = `[](${this.typegen.getCPPReprFor(ktype).std} kk, ${this.typegen.getCPPReprFor(vtype).std} vv) -> ${etyperepr.std} { return ${etyperepr.base}{${this.typegen.getFunctorsForType(ktype).inc}{}(kk), ${this.typegen.getFunctorsForType(vtype).inc}{}(vv)}; }`;

                bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_entries<${ltyperepr}, ${etyperepr.std}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(ltype.trkey)}>(${params[0]}, ${lambdamec});`;
                break;
            }
            case "map_has_all": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);
                const ltype = this.typegen.getCPPReprFor(this.typegen.getMIRType(idecl.params[1].type)).base;

                bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_has_all<${ltype}>(${params[0]}, ${params[1]});`;
                break;
            }
            case "map_domainincludes": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);
                const stype = this.typegen.getCPPReprFor(this.typegen.getMIRType(idecl.params[1].type)).base;

                bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_domainincludes<${stype}>(${params[0]}, ${params[1]});`;
                break;
            }
            case "map_submap": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const kops = this.typegen.getFunctorsForType(ktype);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);
                const vops = this.typegen.getFunctorsForType(vtype);

                const lambdap = this.createLambdaFor(idecl.pcodes.get("p") as MIRPCode);

                bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_submap<${kops.inc}, ${vops.inc}>(${params[0]}, ${lambdap});`;
                break;
            }

            case "map_oftype": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);

                const rmtype = this.typegen.getMIRType(idecl.resultType);
                const rmrepr = this.typegen.getCPPReprFor(rmtype);
                const rmentry = this.getMEntryTypeForMapType(idecl.resultType);

                //TODO: it would be nice if we had specialized versions of these that didn't dump into our scope manager
                const ttype = this.typegen.getMIRType(idecl.binds.get("T") as MIRResolvedTypeKey);
                const codetck = this.generateTypeCheck("kk", ktype, ktype, ttype);
                const lambdatck = `[&${scopevar}](${this.typegen.getCPPReprFor(ktype).std} kk) -> bool { return ${codetck}; }`;

                const utype = this.typegen.getMIRType(idecl.binds.get("U") as MIRResolvedTypeKey);
                const codetcv = this.generateTypeCheck("vv", vtype, vtype, utype);
                const lambdatcv = `[&${scopevar}](${this.typegen.getCPPReprFor(vtype).std} vv) -> bool { return ${codetcv}; }`;

                if(codetck === "false" || codetcv == "false") {
                    bodystr = `auto $$return = BSQ_NEW_ADD_SCOPE(${scopevar}, ${rmtype}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(rmtype.trkey)})`;
                }
                else {
                    //TODO: it would be nice if we had specialized versions of these that didn't dump into our scope manager
                    const codecck = `${this.typegen.getFunctorsForType(ttype).inc}{}(${this.typegen.coerce("kk", ktype, ttype)})`;
                    const codeccv = `${this.typegen.getFunctorsForType(utype).inc}{}(${this.typegen.coerce("vv", vtype, utype)})`;
                    const lambdacc = `[&${scopevar}](${this.typegen.getCPPReprFor(ktype).std} kk, ${this.typegen.getCPPReprFor(vtype).std} vv) -> ${rmentry} { return ${rmentry}{${codecck}, ${codeccv}}; }`;

                    bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_oftype<${rmrepr.base}, ${rmentry}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(rmtype.trkey)}>(${params[0]}, ${lambdatck}, ${lambdatcv}, ${lambdacc});`;
                }
                break;
            }
            case "map_cast": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);

                const rmtype = this.typegen.getMIRType(idecl.resultType);
                const rmrepr = this.typegen.getCPPReprFor(rmtype);
                const rmentry = this.getMEntryTypeForMapType(idecl.resultType);

                //TODO: it would be nice if we had specialized versions of these that didn't dump into our scope manager
                const ttype = this.typegen.getMIRType(idecl.binds.get("T") as MIRResolvedTypeKey);
                const codetck = this.generateTypeCheck("kk", ktype, ktype, ttype);
                const lambdatck = `[&${scopevar}](${this.typegen.getCPPReprFor(ktype).std} kk) -> bool { return ${codetck}; }`;

                const utype = this.typegen.getMIRType(idecl.binds.get("U") as MIRResolvedTypeKey);
                const codetcv = this.generateTypeCheck("vv", vtype, vtype, utype);
                const lambdatcv = `[&${scopevar}](${this.typegen.getCPPReprFor(vtype).std} vv) -> bool { return ${codetcv}; }`;

                if(codetck === "false" || codetcv == "false") {
                    bodystr = `auto $$return = BSQ_NEW_ADD_SCOPE(${scopevar}, ${rmtype}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(rmtype.trkey)})`;
                }
                else {
                    //TODO: it would be nice if we had specialized versions of these that didn't dump into our scope manager
                    const codecck = `${this.typegen.getFunctorsForType(ttype).inc}{}(${this.typegen.coerce("kk", ktype, ttype)})`;
                    const codeccv = `${this.typegen.getFunctorsForType(utype).inc}{}(${this.typegen.coerce("vv", vtype, utype)})`;
                    const lambdacc = `[&${scopevar}](${this.typegen.getCPPReprFor(ktype).std} kk, ${this.typegen.getCPPReprFor(vtype).std} vv) -> ${rmentry} { return ${rmentry}{${codecck}, ${codeccv}}; }`;

                    bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_cast<${rmrepr.base}, ${rmentry}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(rmtype.trkey)}>(${params[0]}, ${lambdatck}, ${lambdatcv}, ${lambdacc});`;
                }
                break;
            }
            case "map_projectall": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);
                const ltype = this.typegen.getCPPReprFor(this.typegen.getMIRType(idecl.params[1].type)).base;

                const kfuncs = this.typegen.getFunctorsForType(ktype);
                const vfuncs = this.typegen.getFunctorsForType(vtype);
                bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_projectall<${ltype}, ${kfuncs.inc}, ${vfuncs.inc}>(${params[0]}, ${params[1]});`;
                break;
            }
            case "map_excludeall": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);
                const ltype = this.typegen.getCPPReprFor(this.typegen.getMIRType(idecl.params[1].type)).base;

                const kfuncs = this.typegen.getFunctorsForType(ktype);
                const vfuncs = this.typegen.getFunctorsForType(vtype);
                bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_excludeall<${ltype}, ${kfuncs.inc}, ${vfuncs.inc}>(${params[0]}, ${params[1]});`;
                break;
            }
            case "map_project": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);
                const stype = this.typegen.getCPPReprFor(this.typegen.getMIRType(idecl.params[1].type)).base;

                const kfuncs = this.typegen.getFunctorsForType(ktype);
                const vfuncs = this.typegen.getFunctorsForType(vtype);
                bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_project<${stype}, ${kfuncs.inc}, ${vfuncs.inc}>(${params[0]}, ${params[1]});`;
                break;
            }
            case "map_exclude": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);
                const stype = this.typegen.getCPPReprFor(this.typegen.getMIRType(idecl.params[1].type)).base;

                const kfuncs = this.typegen.getFunctorsForType(ktype);
                const vfuncs = this.typegen.getFunctorsForType(vtype);
                bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_exclude<${stype}, ${kfuncs.inc}, ${vfuncs.inc}>(${params[0]}, ${params[1]});`;
                break;
            }
            case "map_remap": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);
            
                const rtype = this.typegen.getMIRType(idecl.resultType);
                const rtyperepr = this.typegen.getCPPReprFor(rtype);
                const utype = (this.typegen.assembly.entityDecls.get(rtype.trkey) as MIREntityTypeDecl).terms.get("V") as MIRType;
                const utyperepr = this.typegen.getCPPReprFor(utype);

                const lambdascope = this.typegen.mangleStringForCpp("$lambda_scope$");
                const lambdaf = this.createLambdaFor(idecl.pcodes.get("f") as MIRPCode, lambdascope);

                bodystr = `BSQRefScope ${lambdascope}(true); auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_remap<${rtyperepr.base}, ${utyperepr.std}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(rtype.trkey)}, ${this.typegen.getFunctorsForType(ktype).inc}>(${params[0]}, ${lambdaf});`;
                break;
            }
            case "map_composewith": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);
            
                const rtype = this.typegen.getMIRType(idecl.resultType);
                const rtyperepr = this.typegen.getCPPReprFor(rtype);
                const utype = (this.typegen.assembly.entityDecls.get(rtype.trkey) as MIREntityTypeDecl).terms.get("V") as MIRType;
                const utyperepr = this.typegen.getCPPReprFor(utype);

                const maputype = this.typegen.getMIRType(idecl.params[1].type);
                const maputyperepr = this.typegen.getCPPReprFor(maputype);

                bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_compose<${rtyperepr.base}, ${utyperepr.std}, ${this.typegen.getFunctorsForType(utype).inc}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(rtype.trkey)}, ${this.typegen.getFunctorsForType(ktype).inc}, ${maputyperepr.base}>(${params[0]}, ${params[1]});`;
                break;
            }
            case "map_trycomposewith": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);
            
                const rtype = this.typegen.getMIRType(idecl.resultType);
                const rtyperepr = this.typegen.getCPPReprFor(rtype);
                const utype = (this.typegen.assembly.entityDecls.get(idecl.params[1].type) as MIREntityTypeDecl).terms.get("V") as MIRType;
                const utyperepr = this.typegen.getCPPReprFor(utype);

                const mutype = this.getMapValueContentsInfoForMapType(idecl.resultType);
                const mutyperepr = this.typegen.getCPPReprFor(mutype);

                const maputype = this.typegen.getMIRType(idecl.params[1].type);
                const maputyperepr = this.typegen.getCPPReprFor(maputype);

                //TODO: it would be nice if we had specialized versions of these that didn't dump into our scope manager
                const codecc = this.typegen.coerce("ccu", utype, mutype);
                const lambdaconv = `[&${scopevar}](${utyperepr.std} ccu) -> ${mutyperepr.std} { return ${codecc}; }`;
                const unone = this.typegen.coerce("BSQ_VALUE_NONE", this.typegen.noneType, mutype);

                bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_trycompose<${rtyperepr.base}, ${utyperepr.std}, ${mutyperepr.std}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(rtype.trkey)}, ${this.typegen.getFunctorsForType(ktype).inc}, ${maputyperepr.base}>(${params[0]}, ${params[1]}, ${unone}, ${lambdaconv});`;
                break;
            }
            case "map_defaultcomposewith": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);
            
                const rtype = this.typegen.getMIRType(idecl.resultType);
                const rtyperepr = this.typegen.getCPPReprFor(rtype);
                const utype = (this.typegen.assembly.entityDecls.get(rtype.trkey) as MIREntityTypeDecl).terms.get("V") as MIRType;
                const utyperepr = this.typegen.getCPPReprFor(utype);

                const maputype = this.typegen.getMIRType(idecl.params[1].type);
                const maputyperepr = this.typegen.getCPPReprFor(maputype);

                bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_defaultcompose<${rtyperepr.base}, ${utyperepr.std}, ${this.typegen.getFunctorsForType(utype).inc}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(rtype.trkey)}, ${this.typegen.getFunctorsForType(ktype).inc}, ${maputyperepr.base}>(${params[0]}, ${params[1]}, ${params[2]});`;
                break;
            }
            case "map_invertinj": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const kops = this.typegen.getFunctorsForType(ktype);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);
                const vops = this.typegen.getFunctorsForType(vtype);
                
                const rtype = this.typegen.getMIRType(idecl.resultType);
                const rtyperepr = this.typegen.getCPPReprFor(rtype);

                bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_injinvert<${rtyperepr.base}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(rtype.trkey)}, ${kops.inc}, ${vops.inc}, ${vops.less}, ${vops.eq}>(${params[0]});`;
                break;
            }
            case "map_invertrel": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const kops = this.typegen.getFunctorsForType(ktype);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);
                const vops = this.typegen.getFunctorsForType(vtype);
                
                const rtype = this.typegen.getMIRType(idecl.resultType);
                const rtyperepr = this.typegen.getCPPReprFor(rtype);

                const ltype = (this.typegen.assembly.entityDecls.get(rtype.trkey) as MIREntityTypeDecl).terms.get("V") as MIRType;
                const ltyperepr = this.typegen.getCPPReprFor(ltype);

                bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_relinvert<${ltyperepr.base}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(ltype.trkey)}, ${rtyperepr.base}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(rtype.trkey)}, ${kops.inc}, ${vops.inc}, ${vops.less}>(${params[0]});`;
                break;
            }
            case "map_union": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const kops = this.typegen.getFunctorsForType(ktype);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);
                const vops = this.typegen.getFunctorsForType(vtype);

                bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_union<${kops.inc}, ${vops.inc}>(${params[0]}, ${params[1]});`;
                break;
            }
            case "map_unionall": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const kops = this.typegen.getFunctorsForType(ktype);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);
                const vops = this.typegen.getFunctorsForType(vtype);

                const rtype = this.typegen.getMIRType(idecl.resultType);
                const ltyperepr = this.typegen.getCPPReprFor(this.typegen.getMIRType(idecl.params[0].type));

                bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_unionall<${ltyperepr.base}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(rtype.trkey)}, ${kops.inc}, ${vops.inc}>(${params[0]});`;
                break;
            }
            case "map_merge": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const kops = this.typegen.getFunctorsForType(ktype);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);
                const vops = this.typegen.getFunctorsForType(vtype);

                bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_merge<${kops.inc}, ${vops.inc}>(${params[0]}, ${params[1]});`;
                break;
            }
            case "map_mergeall": {
                const mtype = this.getEnclosingMapTypeForMapOp(idecl);
                const ktype = this.getMapKeyContentsInfoForMapOp(idecl);
                const kops = this.typegen.getFunctorsForType(ktype);
                const vtype = this.getMapValueContentsInfoForMapOp(idecl);
                const vops = this.typegen.getFunctorsForType(vtype);

                const rtype = this.typegen.getMIRType(idecl.resultType);
                const ltyperepr = this.typegen.getCPPReprFor(this.typegen.getMIRType(idecl.params[0].type));

                bodystr = `auto $$return = ${this.createMapOpsFor(mtype, ktype, vtype)}::map_mergeall<${ltyperepr.base}, MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(rtype.trkey)}, ${kops.inc}, ${vops.inc}>(${params[0]});`;
                break;
            }
            case "iteration_while": {
                assert(false, `Need to implement -- ${idecl.iname}`);
                break;
            }
            case "iteration_until": {
                assert(false, `Need to implement -- ${idecl.iname}`);
                break;
            }
            case "iteration_steps": {
                const statetype = this.typegen.getMIRType(idecl.binds.get("S") as string);
                const staterepr = this.typegen.getCPPReprFor(statetype);
                const statefuncs = this.typegen.getFunctorsForType(statetype);

                const lambdascope = this.typegen.mangleStringForCpp("$lambda_scope$");
                const lambdastep = this.createLambdaFor(idecl.pcodes.get("step") as MIRPCode, lambdascope);

                const header = `BSQRefScope ${lambdascope}(true); ${staterepr.std} cacc = ${params[0]};`
                const ctrl = `for(int64_t i = 0; i < ${params[1]}; ++i)`;

                const rcstatus = this.typegen.getRefCountableStatus(statetype);
                const bodynorc = `{ cacc = ${lambdastep}(cacc); }`;
                const bodyrc = `{ ${staterepr.std} nacc = ${lambdastep}(cacc); ${statefuncs.dec}{}(cacc); cacc = nacc; }`;

                bodystr = `${header} ${ctrl} ${rcstatus === "no" ? bodynorc : bodyrc} auto $$return = cacc;`;
                break;
            }
            case "iteration_reduce": {
                const ttype = this.typegen.getMIRType(idecl.binds.get("T") as string);
                const trepr = this.typegen.getCPPReprFor(ttype);
                const tfuncs = this.typegen.getFunctorsForType(ttype);

                const lambdascope = this.typegen.mangleStringForCpp("$lambda_scope$");
                const lambdaop = this.createLambdaFor(idecl.pcodes.get("op") as MIRPCode, lambdascope);

                const header = `BSQRefScope ${lambdascope}(true); ${trepr.std} cacc = ${params[0]};`
                const ctrl = `for(size_t i = 0; i < ${params[1]}->entries.size(); ++i)`;

                const rcstatus = this.typegen.getRefCountableStatus(ttype);
                const bodynorc = `{ cacc = ${lambdaop}(cacc, ${params[1]}->entries[i]); }`;
                const bodyrc = `{ ${trepr.std} nacc = ${lambdaop}(cacc, ${params[1]}->entries[i]); ${tfuncs.dec}{}(cacc); cacc = nacc; }`;

                bodystr = `${header} ${ctrl} ${rcstatus === "no" ? bodynorc : bodyrc} auto $$return = cacc;`;
                break;
            }
            default: {
                assert(false, `Need to implement -- ${idecl.iname}`);
                break;
            }
        }

        const refscope = `BSQRefScope ${scopevar};`;
        let returnmgr = "";
        if (this.typegen.getRefCountableStatus(this.currentRType) !== "no") {
            returnmgr = this.typegen.buildReturnOpForType(this.currentRType, "$$return", "$callerscope$") + ";";
        }

        return "\n    " + refscope + "\n    " + bodystr + "\n    " + returnmgr + "\n    " + "return $$return;\n";
    }
}

export {
    CPPBodyEmitter
};
