//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIRInvokeDecl, MIRInvokeBodyDecl, MIRInvokePrimitiveDecl, MIRConstantDecl, MIRFieldDecl, MIREntityTypeDecl, MIRFunctionParameter, MIREntityType, MIRTupleType, MIRRecordType, MIRRecordTypeEntry, MIRConceptType } from "../../compiler/mir_assembly";
import { CPPTypeEmitter } from "./cpptype_emitter";
import { MIRArgument, MIRRegisterArgument, MIRConstantNone, MIRConstantFalse, MIRConstantTrue, MIRConstantInt, MIRConstantArgument, MIRConstantString, MIROp, MIROpTag, MIRLoadConst, MIRAccessArgVariable, MIRAccessLocalVariable, MIRInvokeFixedFunction, MIRPrefixOp, MIRBinOp, MIRBinEq, MIRBinCmp, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRRegAssign, MIRTruthyConvert, MIRLogicStore, MIRVarStore, MIRReturnAssign, MIRDebug, MIRJump, MIRJumpCond, MIRJumpNone, MIRAbort, MIRBasicBlock, MIRPhi, MIRConstructorTuple, MIRConstructorRecord, MIRAccessFromIndex, MIRAccessFromProperty, MIRInvokeKey, MIRAccessConstantValue, MIRLoadFieldDefaultValue, MIRBody, MIRConstructorPrimary, MIRBodyKey, MIRAccessFromField, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionSingletons, MIRIsTypeOf } from "../../compiler/mir_ops";
import * as assert from "assert";
import { topologicalOrder } from "../../compiler/mir_info";
import { constructCallGraphInfo, CallGInfo } from "../../compiler/mir_callg";
import { MIRKeyGenerator } from "../../compiler/mir_emitter";
import { CoreImplBodyText } from "./cppcore_impls";

function NOT_IMPLEMENTED<T>(msg: string): T {
    throw new Error(`Not Implemented: ${msg}`);
}

function filenameClean(file: string): string {
    return file.replace(/[\\]/g, "/");
}

class CPPBodyEmitter {
    readonly assembly: MIRAssembly;
    readonly typegen: CPPTypeEmitter;
    readonly callg: CallGInfo;

    readonly allPropertyNames: Set<string> = new Set<string>();
    readonly allConstStrings: Map<string, string> = new Map<string, string>();

    private currentFile: string = "[No File]";
    private currentRType: MIRType;

    private vtypes: Map<string, MIRType> = new Map<string, MIRType>();
    private generatedBlocks: Map<string, string[]> = new Map<string, string[]>();

    private subtypeOrderCtr = 0;
    subtypeFMap: Map<string, {order: number, decl: string}> = new Map<string, {order: number, decl: string}>();

    private compoundEqualityOps: { fkey: string, t1: MIRType, t2: MIRType }[] = [];
    private compoundLTOps: { fkey: string, t1: MIRType, t2: MIRType }[] = [];
    private compoundLTEQOps: { fkey: string, t1: MIRType, t2: MIRType }[] = [];

    constructor(assembly: MIRAssembly, typegen: CPPTypeEmitter) {
        this.assembly = assembly;
        this.typegen = typegen;
        this.callg = constructCallGraphInfo(assembly.entryPoints, assembly);

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
        const isinlineable = this.typegen.isPrimitiveType(into);

        if (cval instanceof MIRConstantNone) {
            return this.typegen.coerce("BSQ_VALUE_NONE", this.typegen.noneType, into);
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

            return `(&Runtime::${this.allConstStrings.get(sval) as string})`;
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
        const fvals = cp.args.map((arg, i) => {
            const ftype = this.typegen.getMIRType(ctype.fields[i].declaredType);
            return this.typegen.generateConstructorArgInc(ftype, this.argToCpp(arg, ftype));
        });

        const smtctype = this.typegen.typeToCPPType(this.typegen.getMIRType(cp.tkey), "base");
        const scopevar = this.varNameToCppName("$scope$");
        const cexp = `${this.varToCppName(cp.trgt)} = ${scopevar}.addAllocRef<${this.typegen.scopectr++}, ${smtctype}>(new ${smtctype}(${fvals.join(", ")}));`;
        if (ctype.invariants.length === 0) {
            return cexp;
        }
        else {
            const testexp = `${this.typegen.mangleStringForCpp("invariant::" + cp.tkey)}(${this.varToCppName(cp.trgt)});`;
            return cexp + " " + testexp;
        }
    }

    generateMIRConstructorPrimaryCollectionEmpty(cpce: MIRConstructorPrimaryCollectionEmpty): string {
        const ctype = this.assembly.entityDecls.get((this.typegen.getMIRType(cpce.tkey).options[0] as MIREntityType).ekey) as MIREntityTypeDecl;
        const itrgt = this.invokenameToCPP(MIRKeyGenerator.generateBodyKey("const", MIRKeyGenerator.generateConstKey_MIR(ctype, "empty")));
        if (ctype.name === "List") {
            return `${this.varToCppName(cpce.trgt)} = ${itrgt}();`;
        }
        else if (ctype.name === "Set") {
            return `${this.varToCppName(cpce.trgt)} = ${itrgt}();`;
        }
        else {
            return `${this.varToCppName(cpce.trgt)} = ${itrgt}();`;
        }
    }

    generateMIRConstructorPrimaryCollectionSingletons(cpcs: MIRConstructorPrimaryCollectionSingletons): string {
        const ctype = this.assembly.entityDecls.get((this.typegen.getMIRType(cpcs.tkey).options[0] as MIREntityType).ekey) as MIREntityTypeDecl;
        if (ctype.name === "List") {
            const clisttype = this.typegen.getMIRType((ctype.fields.find((fd) => fd.name === "list") as MIRFieldDecl).declaredType);
            const clistcons = `new ${this.typegen.mangleStringForCpp(clisttype.options[0].trkey)}`;
            const contentstype = ctype.terms.get("T") as MIRType;

            let cons = "BSQ_VALUE_NONE";
            for (let i = cpcs.args.length - 1; i >= 0; --i) {
                cons = `${clistcons}(${this.typegen.generateConstructorArgInc(contentstype, this.argToCpp(cpcs.args[i], contentstype))}, BSQRef::checkedIncrementNoneable<${this.typegen.typeToCPPType(clisttype, "base")}>(${cons}))`;
            }

            const lcname = this.invokenameToCPP(MIRKeyGenerator.generateStaticKey_MIR(ctype, "_cons"));
            const scopevar = this.varNameToCppName("$scope$");
            return `${this.varToCppName(cpcs.trgt)} = ${lcname}(${cpcs.args.length}, ${cons}, ${scopevar}.getCallerSlot<${this.typegen.scopectr++}>());`;
        }
        else if (ctype.name === "Set") {
            return NOT_IMPLEMENTED<string>("generateMIRConstructorPrimaryCollectionSingletons -- Set");
        }
        else {
            return NOT_IMPLEMENTED<string>("generateMIRConstructorPrimaryCollectionSingletons -- Map");
        }
    }

    generateMIRAccessFromIndex(op: MIRAccessFromIndex, resultAccessType: MIRType): string {
        const tuptype = this.getArgType(op.arg);
        if (this.typegen.isKnownLayoutTupleType(tuptype)) {
            const ftuptype = CPPTypeEmitter.getKnownLayoutTupleType(tuptype);
            if (op.idx < ftuptype.entries.length) {
                const value = `(${this.argToCpp(op.arg, tuptype)})${this.typegen.generateFixedTupleAccessor(op.idx)}`;
                return `${this.varToCppName(op.trgt)} = ${this.typegen.coerce(value, this.typegen.anyType, resultAccessType)};`;
            }
            else {
                return `${this.varToCppName(op.trgt)} = BSQ_VALUE_NONE;`;
            }
        }
        else if (this.typegen.isTupleType(tuptype)) {
            const maxlen = CPPTypeEmitter.getTupleTypeMaxLength(tuptype);
            if (op.idx < maxlen) {
                const value = `(${this.argToCpp(op.arg, tuptype)})${this.typegen.generateFixedTupleAccessor(op.idx)}`;
                return `${this.varToCppName(op.trgt)} = ${this.typegen.coerce(value, this.typegen.anyType, resultAccessType)};`;
            }
            else {
                return `${this.varToCppName(op.trgt)} = BSQ_VALUE_NONE;`;
            }
        }
        else {
            const value = `BSQ_GET_VALUE_PTR(${this.argToCpp(op.arg, this.typegen.anyType)}, BSQTuple)->atFixed<${op.idx}>()`;
            return `${this.varToCppName(op.trgt)} = ${this.typegen.coerce(value, this.typegen.anyType, resultAccessType)};`;
        }
    }

    generateMIRAccessFromProperty(op: MIRAccessFromProperty, resultAccessType: MIRType): string {
        const rectype = this.getArgType(op.arg);
        if (this.typegen.isKnownLayoutRecordType(rectype)) {
            const frectype = CPPTypeEmitter.getKnownLayoutRecordType(rectype);
            if (frectype.entries.some((entry) => entry.name === op.property)) {
                const value = `(${this.argToCpp(op.arg, rectype)})${this.typegen.generateKnownRecordAccessor(rectype, op.property)}`;
                return `${this.varToCppName(op.trgt)} = ${this.typegen.coerce(value, this.typegen.anyType, resultAccessType)};`;
            }
            else {
                return `${this.varToCppName(op.trgt)} = BSQ_VALUE_NONE;`;
            }
        }
        else if (this.typegen.isRecordType(rectype)) {
            const maxset = CPPTypeEmitter.getRecordTypeMaxPropertySet(rectype);
            if (maxset.some((pname) => pname === op.property)) {
                const value = `(${this.argToCpp(op.arg, rectype)})${this.typegen.generateFixedRecordAccessor(op.property)}`;
                return `${this.varToCppName(op.trgt)} = ${this.typegen.coerce(value, this.typegen.anyType, resultAccessType)};`;
            }
            else {
                return `${this.varToCppName(op.trgt)} = BSQ_VALUE_NONE;`;
            }
        }
        else {
            const value = `BSQ_GET_VALUE_PTR(${this.argToCpp(op.arg, this.typegen.anyType)}, BSQRecord)->atFixed<MIRPropertyEnum::${op.property}>()`;
            return `${this.varToCppName(op.trgt)} = ${this.typegen.coerce(value, this.typegen.anyType, resultAccessType)};`;
        }
    }

    generateMIRAccessFromField(op: MIRAccessFromField, resultAccessType: MIRType): string {
        const argtype = this.getArgType(op.arg);

        if (this.typegen.isUEntityType(argtype)) {
            const etype = CPPTypeEmitter.getUEntityType(argtype);
            const entity = this.assembly.entityDecls.get(etype.ekey) as MIREntityTypeDecl;
            const field = entity.fields.find((f) => f.name === op.field) as MIRFieldDecl;

            const access = `${this.argToCpp(op.arg, argtype)}->${op.field}`;
            return `${this.varToCppName(op.trgt)} = ${this.typegen.coerce(access, this.typegen.getMIRType(field.declaredType), resultAccessType)};`;
        }
        else {
            const access = `BSQ_GET_VALUE_PTR(${this.argToCpp(op.arg, this.typegen.anyType)}, BSQRef)->get$${op.field}()`;
            return `${this.varToCppName(op.trgt)} = ${this.typegen.coerce(access, this.typegen.anyType, resultAccessType)};`;
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
            const scopevar = this.varNameToCppName("$scope$");
            vals.push(`${scopevar}.getCallerSlot<${this.typegen.scopectr++}>()`);
        }

        return `${this.varToCppName(ivop.trgt)} = ${this.invokenameToCPP(ivop.mkey)}(${vals.join(", ")});`;
    }

    registerCompoundEquals(t1: MIRType, t2: MIRType): string {
        const lt = (t1.trkey < t2.trkey) ? t1 : t2;
        const rt = (t1.trkey < t2.trkey) ? t2 : t1;

        const fkey = `EQUALS_${this.typegen.mangleStringForCpp(lt.trkey)}_${this.typegen.mangleStringForCpp(rt.trkey)}`;

        if (this.compoundEqualityOps.findIndex((eop) => eop.t1.trkey === lt.trkey && eop.t2.trkey === rt.trkey) === -1) {
            this.compoundEqualityOps.push({ fkey: fkey, t1: lt, t2: rt });
        }

        return fkey;
    }

    generateFastEquals(op: string, lhs: MIRArgument, rhs: MIRArgument): string {
        const lhvtype = this.getArgType(lhs);
        const rhvtype = this.getArgType(rhs);

        if (lhvtype.trkey === "NSCore::Bool" && rhvtype.trkey === "NSCore::Bool") {
            return `(${this.argToCpp(lhs, this.typegen.boolType)} ${op} ${this.argToCpp(rhs, this.typegen.boolType)})`;
        }
        else if (lhvtype.trkey === "NSCore::Int" && rhvtype.trkey === "NSCore::Int"){
            return `(${this.argToCpp(lhs, this.typegen.intType)} ${op} ${this.argToCpp(rhs, this.typegen.intType)})`;
        }
        else {
            return `(${this.argToCpp(lhs, this.typegen.stringType)}->sdata ${op} ${this.argToCpp(rhs, this.typegen.stringType)}->sdata)`;
        }
    }

    registerCompoundLT(t1: MIRType, t2: MIRType): string {
        const fkey = `LT_${this.typegen.mangleStringForCpp(t1.trkey)}_${this.typegen.mangleStringForCpp(t2.trkey)}`;

        if (this.compoundLTOps.findIndex((eop) => eop.t1.trkey === t1.trkey && eop.t2.trkey === t2.trkey) === -1) {
            this.compoundLTOps.push({ fkey: fkey, t1: t1, t2: t2 });
        }

        return fkey;
    }

    registerCompoundLTEQ(t1: MIRType, t2: MIRType): string {
        const fkey = `LTEQ_${this.typegen.mangleStringForCpp(t1.trkey)}_${this.typegen.mangleStringForCpp(t2.trkey)}`;

        if (this.compoundLTEQOps.findIndex((eop) => eop.t1.trkey === t1.trkey && eop.t2.trkey === t2.trkey) === -1) {
            this.compoundLTEQOps.push({ fkey: fkey, t1: t1, t2: t2 });
        }

        return fkey;
    }

    generateFastCompare(op: string, lhs: MIRArgument, rhs: MIRArgument): string {
        const lhvtype = this.getArgType(lhs);
        const rhvtype = this.getArgType(rhs);

        if (lhvtype.trkey === "NSCore::Bool" && rhvtype.trkey === "NSCore::Bool") {
            return `(${this.argToCpp(lhs, this.typegen.boolType)} ${op} ${this.argToCpp(rhs, this.typegen.boolType)})`;
        }
        else if (lhvtype.trkey === "NSCore::Int" && rhvtype.trkey === "NSCore::Int"){
            return `(${this.argToCpp(lhs, this.typegen.intType)} ${op} ${this.argToCpp(rhs, this.typegen.intType)})`;
        }
        else {
            return `(${this.argToCpp(lhs, this.typegen.stringType)}->sdata ${op} ${this.argToCpp(rhs, this.typegen.stringType)}->sdata)`;
        }
    }

    generateSubtypeTupleCheck(argv: string, argt: string, size_macro: string, accessor_macro: string, argtype: MIRType, oftype: MIRTupleType): string {
        const subtypesig = `bool subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}(${argt} atuple)`;

        if (this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;

            let reqlen = oftype.entries.findIndex((entry) => entry.isOptional);
            if (reqlen === -1) {
                reqlen = oftype.entries.length;
            }

            const alength = size_macro.replace("ARG", "atuple");
            const lenchk = `if(${alength} < ${reqlen} || ${oftype.entries.length} < ${alength}) return false;`;

            let checks: string[] = [];
            for (let i = 0; i < oftype.entries.length; ++i) {
                if (!oftype.entries[i].isOptional) {
                    if (!(this.typegen.isKnownLayoutTupleType(argtype) && this.typegen.assembly.subtypeOf(CPPTypeEmitter.getKnownLayoutTupleType(argtype).entries[i].type, oftype.entries[i].type))) {
                        checks.push(this.generateTypeCheck(`${accessor_macro.replace("ARG", "atuple").replace("IDX", i.toString())}`, this.typegen.anyType, oftype.entries[i].type, true));
                    }
                }
                else {
                    if (this.typegen.isTupleType(argtype) && CPPTypeEmitter.getTupleTypeMaxLength(argtype) <= i) {
                        const chk = this.generateTypeCheck(`${accessor_macro.replace("ARG", "atuple").replace("IDX", i.toString())}`, this.typegen.anyType, oftype.entries[i].type, true);
                        checks.push(`(${alength} <= ${i} || ${chk})`);
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
                    op = `(${checks.join(" && ")})`;
                }
            }

            const decl = subtypesig
            + "\n{\n"
            + `    ${lenchk} \n\n`
            + `    return ${op};\n`
            + `}\n`;

            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }

        return `subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}(${argv})`;
    }

    generateSubtypeRecordCheck(argv: string, argt: string, size_macro: string, accessor_macro: string, has_macro: string, argtype: MIRType, oftype: MIRRecordType): string {
        const subtypesig = `bool subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}(${argt} arecord)`;

        if (this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;

            let reqlen = oftype.entries.filter((entry) => !entry.isOptional);
            const alength = size_macro.replace("ARG", "arecord");
            const lenchk = `if(${alength} < ${reqlen} || ${oftype.entries.length} < ${alength}) return false;`;

            let checks: string[] = [];
            for (let i = 0; i < oftype.entries.length; ++i) {
                const pname = oftype.entries[i].name;
                if (!oftype.entries[i].isOptional) {
                    if (!(this.typegen.isKnownLayoutRecordType(argtype) && this.typegen.assembly.subtypeOf((CPPTypeEmitter.getKnownLayoutRecordType(argtype).entries.find((e) => e.name === pname) as MIRRecordTypeEntry).type, oftype.entries[i].type))) {
                        checks.push(this.generateTypeCheck(`${accessor_macro.replace("ARG", "arecord").replace("PNAME", pname)}`, this.typegen.anyType, oftype.entries[i].type, true));
                    }
                }
                else {
                    const chk = this.generateTypeCheck(`${accessor_macro.replace("ARG", "arecord").replace("PNAME", pname)}`, this.typegen.anyType, oftype.entries[i].type, true);
                    checks.push(`(!${has_macro.replace("ARG", "arecord").replace("PNAME", pname)} || ${chk})`);
                }
            }

            const possibleargproperties = CPPTypeEmitter.getRecordTypeMaxPropertySet(argtype);
            for(let i = 0; i < possibleargproperties.length; ++i) {
                const pname = possibleargproperties[i];
                if(oftype.entries.find((p) => p.name === pname) === undefined) {
                    checks.push(`!${has_macro.replace("ARG", "arecord").replace("PNAME", pname)}`);
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
            + `    ${lenchk} \n\n`
            + `    return ${op};\n`
            + `}\n`;

            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }

        return `subtypeFROM_${this.typegen.mangleStringForCpp(argtype.trkey)}_TO_${this.typegen.mangleStringForCpp(oftype.trkey)}(${argv})`;
    }

    generateFastTupleTypeCheck(arg: string, argtype: MIRType, oftype: MIRTupleType, inline: boolean): string {
        if(this.typegen.isPrimitiveType(argtype)) {
            return "false";
        }
        else if (this.typegen.isTupleType(argtype)) {
            if (this.typegen.isKnownLayoutTupleType(argtype)) {
                const atuple = CPPTypeEmitter.getKnownLayoutTupleType(argtype);
                if(atuple.entries.length === 0) {
                    return "true";
                }
                else if(oftype.entries.length < atuple.entries.length) {
                    return "false";
                }
                else if(oftype.entries.length > atuple.entries.length && !oftype.entries[atuple.entries.length].isOptional) {
                    return "false";
                }
                else {
                    if (inline) {
                        let ttests = atuple.entries.map((entry, i) => this.generateTypeCheck(`(${arg})${this.typegen.generateFixedTupleAccessor(i)}`, this.typegen.anyType, entry.type, false));
                        
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
                                return `(${ttests.join(" && ")})`;
                            }
                        }
                    }
                    else {
                        return this.generateSubtypeTupleCheck(arg, this.typegen.typeToCPPType(argtype, "parameter"), CPPTypeEmitter.getKnownLayoutTupleType(argtype).entries.length.toString(), "ARG.atFixed<IDX>()", argtype, oftype);
                    }
                }
            }
            else {
                return this.generateSubtypeTupleCheck(arg, this.typegen.typeToCPPType(argtype, "parameter"), "ARG.size", "ARG.atFixed<IDX>()", argtype, oftype);
            }
        }
        else if(this.typegen.isRecordType(argtype) || this.typegen.isUEntityType(argtype)) {
            return "false;"
        }
        else {
            assert(this.typegen.typeToCPPType(argtype, "base") === "Value"); 

            const tsc = this.generateSubtypeTupleCheck(`BSQ_GET_VALUE_PTR(${arg}, BSQTuple)`, "BSQTuple*", "ARG->size", "ARG->atFixed<IDX>()", argtype, oftype);
            return `(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQTuple*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr && ${tsc})`
        }
    }

    generateFastRecordTypeCheck(arg: string, argtype: MIRType, oftype: MIRRecordType, inline: boolean): string {
        if(this.typegen.isPrimitiveType(argtype) || this.typegen.isTupleType(argtype)) {
            return "false;"
        }
        else if (this.typegen.isRecordType(argtype)) {
            if (this.typegen.isKnownLayoutRecordType(argtype)) {
                const arecord = CPPTypeEmitter.getKnownLayoutRecordType(argtype);
                if(arecord.entries.length === 0) {
                    return "true";
                }
                else if(arecord.entries.some((entry) => oftype.entries.find((oe) => entry.name ===  oe.name) === undefined)) {
                    return "false";
                }
                else if(oftype.entries.some((entry) => !entry.isOptional && arecord.entries.find((ae) => entry.name ===  ae.name) === undefined)) {
                    return "false";
                }
                else {
                    if (inline) {
                        let ttests = arecord.entries.map((entry) => {
                            const ofentry = oftype.entries.find((oe) => oe.name === entry.name) as MIRRecordTypeEntry;
                            return this.generateTypeCheck(`(${arg})${this.typegen.generateFixedRecordAccessor(entry.name)}`, this.typegen.anyType, ofentry.type, false)
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
                                return `(${ttests.join(" && ")})`;
                            }
                        }
                    }
                    else {
                        const pmacro = `${this.typegen.typeToCPPType(argtype, "base")}::hasProperty<PNAME>(${this.typegen.getKnownPropertyRecordArrayName(argtype)})`;
                        return this.generateSubtypeRecordCheck(arg, this.typegen.typeToCPPType(argtype, "parameter"), CPPTypeEmitter.getKnownLayoutRecordType(argtype).entries.length.toString(), "ARG.atFixed<PNAME>()", pmacro, argtype, oftype);
                    }
                }
            }
            else {
                return this.generateSubtypeRecordCheck(arg, this.typegen.typeToCPPType(argtype, "parameter"), "ARG.size", "ARG.atFixed<PNAME>()", "ARG.hasProperty<PNAME>()", argtype, oftype);
            }
        }
        else if(this.typegen.isUEntityType(argtype)) {
            return "false;"
        }
        else {
            assert(this.typegen.typeToCPPType(argtype, "base") === "Value"); 

            const tsc = this.generateSubtypeRecordCheck(`BSQ_GET_VALUE_PTR(${arg}, BSQRecord)`, "BSQRecord*", "ARG->size", "ARG->atFixed<PNAME>()", "ARG->hasProperty<PNAME>()", argtype, oftype);
            return `(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQRecord*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr && ${tsc})`

        }
    }

    generateFastEntityTypeCheck(arg: string, argtype: MIRType, oftype: MIREntityType): string {
        if(this.typegen.isPrimitiveType(argtype)) {
            return argtype.options[0].trkey === oftype.trkey ? "true" : "false";
        }
        else if(this.typegen.isTupleType(argtype) || this.typegen.isRecordType(argtype)) {
            return "false";
        }
        else if (this.typegen.isUEntityType(argtype)) {
            if(oftype.ekey === "NSCore::None") {
                return `${arg} == nullptr`;
            }
            else {
                return `(${arg})->ntype == MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(oftype.ekey)}`;
            }
        }
        else {
            assert(this.typegen.typeToCPPType(argtype, "base") === "Value");
        
            const ofdecl = this.typegen.assembly.entityDecls.get(oftype.ekey) as MIREntityTypeDecl;

            if(oftype.ekey === "NSCore::None") {
                return `BSQ_IS_VALUE_NONE(${arg})`;
            }
            else if(oftype.ekey === "NSCore::Bool") {
                return `BSQ_IS_VALUE_BOOL(${arg})`;
            }
            else if(oftype.ekey === "NSCore::Int") {
                return `BSQ_IS_VALUE_INT(${arg})`;
            }
            else if(oftype.ekey === "NSCore::String") {
                return `(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQString*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr)`;
            }
            else if(oftype.ekey.startsWith("NSCore::StringOf<")) {
                return `(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQStringOf*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr && dynamic_cast<BSQStringOf*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef))->oftype == MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(oftype.ekey)})`;
            }
            else if(oftype.ekey.startsWith("NSCore::ValidatedString<")) {
                return `(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQValidatedString*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr && dynamic_cast<BSQValidatedString*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef))->oftype == MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(oftype.ekey)})`;
            }
            else if(oftype.ekey.startsWith("NSCore::POBBuffer<")) {
                return `(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQPODBuffer*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr && dynamic_cast<BSQPODBuffer*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef))->oftype == MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(oftype.ekey)})`;
            }
            else if(oftype.ekey === "NSCore::GUID") {
                return `(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQGUID*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr)`;
            }
            else if (ofdecl.provides.includes("NSCore::Enum")) {
                return `(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQEnum*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr && dynamic_cast<BSQEnum*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef))->oftype == MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(oftype.ekey)})`;
            }
            else if (ofdecl.provides.includes("NSCore::IdKey")) {
                return `(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQIdKey*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr && dynamic_cast<BSQIdKey*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef))->oftype == MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(oftype.ekey)})`;
            }
            else if(oftype.ekey === "NSCore::Regex") {
                return `(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQRegex*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr)`;
            }
            else {
                return `(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQObject*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr && BSQ_GET_VALUE_PTR(${arg}, BSQObject)->ntype == MIRNominalTypeEnum::${this.typegen.mangleStringForCpp(oftype.ekey)})`;
            }
        }
    }

    generateFastConceptTypeCheck(arg: string, argtype: MIRType, oftype: MIRConceptType): string {
        let tests: string[] = [];

        if(oftype.trkey === "NSCore::Any") {
            tests.push("true");
        }
        else if(oftype.trkey === "NSCore::Some") {
            if(this.typegen.isPrimitiveType(argtype) || this.typegen.isTupleType(argtype) || this.typegen.isRecordType(argtype)) {
                tests.push("true");
            }
            else if (this.typegen.isUEntityType(argtype)) {
                if(this.typegen.assembly.subtypeOf(this.typegen.noneType, argtype)) {
                    tests.push(`${arg} != nullptr`)
                }
            }
            else {
                tests.push(`BSQ_IS_VALUE_NONNONE(${arg})`);
            }
        }
        else if(this.typegen.isPrimitiveType(argtype)) {
            tests.push(...[this.typegen.boolType, this.typegen.intType, this.typegen.stringType].map((spe) => this.generateFastEntityTypeCheck(arg, argtype, spe.options[0] as MIREntityType)));
        }
        else if(this.typegen.isTupleType(argtype)) {
            tests.push(this.assembly.subtypeOf(this.typegen.getMIRType("NSCore::Tuple"), this.typegen.getMIRType(oftype.trkey)) ? "true" : "false");
        }
        else if(this.typegen.isRecordType(argtype)) {
            tests.push(this.assembly.subtypeOf(this.typegen.getMIRType("NSCore::Record"), this.typegen.getMIRType(oftype.trkey)) ? "true" : "false");
        }
        else if (this.typegen.isUEntityType(argtype)) {
            if(this.typegen.assembly.subtypeOf(this.typegen.noneType, argtype) && this.typegen.assembly.subtypeOf(this.typegen.noneType, this.typegen.getMIRType(oftype.trkey))) {
                tests.push(`${arg} == nullptr`)
            }
            else {
                tests.push(`BSQObject::checkSubtype<${this.typegen.getSubtypesArrayCount(oftype)}>((${arg})->ntype, MIRConceptSubtypeArray__${this.typegen.mangleStringForCpp(oftype.trkey)})`);
            }
        }
        else {
            assert(this.typegen.typeToCPPType(argtype, "base") === "Value");

            let allspecialentities: MIREntityType[] = [];
            this.typegen.assembly.entityDecls.forEach((etd) => {
                if(!this.typegen.doDefaultEmitOnEntity(etd) && oftype.ckeys.every((ct) => this.assembly.subtypeOf(this.typegen.getMIRType(etd.tkey), this.typegen.getMIRType(ct)))) {
                    allspecialentities.push(this.typegen.getMIRType(etd.tkey).options[0] as MIREntityType);
                }
            });

            if(allspecialentities.find((stype) => stype.ekey === "NSCore::None") !== undefined) {
                tests.push(this.generateFastEntityTypeCheck(arg, argtype, allspecialentities.find((stype) => stype.trkey === "NSCore::None") as MIREntityType));
            }
            if(allspecialentities.find((stype) => stype.ekey === "NSCore::Bool") !== undefined) {
                tests.push(this.generateFastEntityTypeCheck(arg, argtype, allspecialentities.find((stype) => stype.trkey === "NSCore::Bool") as MIREntityType));
            }
            if(allspecialentities.find((stype) => stype.ekey === "NSCore::Int") !== undefined) {
                tests.push(this.generateFastEntityTypeCheck(arg, argtype, allspecialentities.find((stype) => stype.trkey === "NSCore::Int") as MIREntityType));
            }
            if(allspecialentities.find((stype) => stype.ekey === "NSCore::String") !== undefined) {
                tests.push(this.generateFastEntityTypeCheck(arg, argtype, allspecialentities.find((stype) => stype.trkey === "NSCore::String") as MIREntityType));
            }
            if(allspecialentities.find((stype) => stype.ekey.startsWith("NSCore::StringOf<")) !== undefined) {
                tests.push(`(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQStringOf*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr)`);
            }
            if(allspecialentities.find((stype) => stype.ekey.startsWith("NSCore::ValidatedString<")) !== undefined) {
                tests.push(`(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQValidatedString*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr)`);
            }
            if(allspecialentities.find((stype) => stype.ekey.startsWith("NSCore::POBBuffer<")) !== undefined) {
                tests.push(`(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQPODBuffer*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr)`);
            }
            if(allspecialentities.find((stype) => stype.ekey === "NSCore::GUID") !== undefined) {
                tests.push(this.generateFastEntityTypeCheck(arg, argtype, allspecialentities.find((stype) => stype.trkey === "NSCore::GUID") as MIREntityType));
            }
            if(allspecialentities.find((stype) => (this.assembly.entityDecls.get(stype.ekey) as MIREntityTypeDecl).provides.includes("NSCore::Enum")) !== undefined) {
                tests.push(`(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQEnum*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr)`);
            }
            if(allspecialentities.find((stype) => (this.assembly.entityDecls.get(stype.ekey) as MIREntityTypeDecl).provides.includes("NSCore::IdKey")) !== undefined) {
                tests.push(`(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQIdKey*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr)`);
            }
            if(allspecialentities.find((stype) => stype.ekey === "NSCore::Regex") !== undefined) {
                tests.push(this.generateFastEntityTypeCheck(arg, argtype, allspecialentities.find((stype) => stype.trkey === "NSCore::Regex") as MIREntityType));
            }

            if(this.assembly.subtypeOf(this.typegen.getMIRType("NSCore::Tuple"), this.typegen.getMIRType(oftype.trkey))) {
                tests.push(`(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQTuple*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr)`);
            }
            if(this.assembly.subtypeOf(this.typegen.getMIRType("NSCore::Record"), this.typegen.getMIRType(oftype.trkey))) {
                tests.push(`(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQRecord*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr)`);
            }
            //array, podX, Dict also here 

            tests.push(`(BSQ_IS_VALUE_PTR(${arg}) && dynamic_cast<BSQObject*>(BSQ_GET_VALUE_PTR(${arg}, BSQRef)) != nullptr && BSQObject::checkSubtype<${this.typegen.getSubtypesArrayCount(oftype)}>(BSQ_GET_VALUE_PTR(${arg}, BSQObject)->ntype, MIRConceptSubtypeArray__${this.typegen.mangleStringForCpp(oftype.trkey)}))`);
        }

        tests = tests.filter((t) => t !== "false");
        if(tests.includes("true")) {
            return "true";
        }
        else if(tests.length === 0) {
            return "false";
        }
        else if(tests.length === 1) {
            return tests[0];
        }
        else {
            return `(${tests.join(" || ")})`;
        }
    }

    generateTypeCheck(arg: string, argtype: MIRType, oftype: MIRType, inline: boolean): string {
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
                return this.generateFastTupleTypeCheck(arg, argtype, topt, inline);
            }
            else {
                assert(topt instanceof MIRRecordType);

                return this.generateFastRecordTypeCheck(arg, argtype, topt as MIRRecordType, inline);
            }
        })
        .filter((test) => test !== "false");

        if(tests.includes("true") || tests.length === 0) {
            return "true";
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
                return NOT_IMPLEMENTED<string>("MIRLoadConstTypedString");
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
                const tc = op as MIRConstructorTuple;
                const args = tc.args.map((arg) => this.argToCpp(arg, this.typegen.anyType));

                if (this.typegen.isKnownLayoutTupleType(this.typegen.getMIRType(tc.resultTupleType))) {
                    return `${this.varToCppName(tc.trgt)} = { ${args.join(", ")} };`;
                }
                else {
                    return `${this.varToCppName(tc.trgt)} = { ${[args.length, ...args].join(", ")} };`;
                }
            }
            case MIROpTag.MIRConstructorRecord: {
                const tr = op as MIRConstructorRecord;

                if (this.typegen.isKnownLayoutRecordType(this.typegen.getMIRType(tr.resultRecordType))) {
                    const args = tr.args.map((arg) => this.argToCpp(arg[1], this.typegen.anyType));
                    return `${this.varToCppName(tr.trgt)} = { ${args.join(", ")} };`;
                }
                else {
                    const args = tr.args.map((arg) => `std::make_pair(MIRPropertyEnum::${this.typegen.mangleStringForCpp(arg[0])}, ${this.argToCpp(arg[1], this.typegen.anyType)})`);
                    return `${this.varToCppName(tr.trgt)} = { ${[args.length, ...args].join(", ")} };`;
                }
            }
            case MIROpTag.MIRAccessFromIndex: {
                const ai = op as MIRAccessFromIndex;
                return this.generateMIRAccessFromIndex(ai, this.typegen.getMIRType(ai.resultAccessType));
            }
            case MIROpTag.MIRProjectFromIndecies: {
                return NOT_IMPLEMENTED<string>("MIRProjectFromIndecies");
            }
            case MIROpTag.MIRAccessFromProperty: {
                const ap = op as MIRAccessFromProperty;
                return this.generateMIRAccessFromProperty(ap, this.typegen.getMIRType(ap.resultAccessType));
            }
            case MIROpTag.MIRProjectFromProperties: {
                return NOT_IMPLEMENTED<string>("MIRProjectFromProperties");
            }
            case MIROpTag.MIRAccessFromField: {
                const af = op as MIRAccessFromField;
                return this.generateMIRAccessFromField(af, this.typegen.getMIRType(af.resultAccessType));
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
                        return `${this.varToCppName(pfx.trgt)} = -${this.argToCpp(pfx.arg, this.typegen.intType)};`;
                    }
                    else {
                        return `${this.varToCppName(pfx.trgt)} = ${this.argToCpp(pfx.arg, this.typegen.intType)};`;
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
                if (this.typegen.isPrimitiveType(lhvtype) && this.typegen.isPrimitiveType(rhvtype)) {
                    return `${this.varToCppName(beq.trgt)} = ${this.generateFastEquals(beq.op, beq.lhs, beq.rhs)};`;
                }
                else {
                    const larg = this.argToCpp(beq.lhs, lhvtype);
                    const rarg = this.argToCpp(beq.rhs, rhvtype);

                    const compoundeq = `${this.registerCompoundEquals(lhvtype, rhvtype)}(${larg} ${rarg})`;
                    return `${this.varToCppName(beq.trgt)} = ${beq.op === "!=" ? "!" : ""}${compoundeq};`;
                }
            }
            case MIROpTag.MIRBinCmp: {
                const bcmp = op as MIRBinCmp;

                const lhvtype = this.getArgType(bcmp.lhs);
                const rhvtype = this.getArgType(bcmp.rhs);

                if (this.typegen.isPrimitiveType(lhvtype) && this.typegen.isPrimitiveType(rhvtype)) {
                    return `${this.varToCppName(bcmp.trgt)} = ${this.generateFastCompare(bcmp.op, bcmp.lhs, bcmp.rhs)};`;
                }
                else {
                    const larg = this.argToCpp(bcmp.lhs, lhvtype);
                    const rarg = this.argToCpp(bcmp.rhs, rhvtype);

                    if (bcmp.op === "<") {
                        const compoundlt = `${this.registerCompoundLT(lhvtype, rhvtype)}(${larg} ${rarg})`;
                        return `${this.varToCppName(bcmp.trgt)} = ${compoundlt};`;
                    }
                    else if (bcmp.op === ">") {
                        const compoundlt = `(${this.registerCompoundLT(lhvtype, rhvtype)} ${rarg} ${larg})`;
                        return `${this.varToCppName(bcmp.trgt)} = ${compoundlt};`;
                    }
                    else if (bcmp.op === "<=") {
                        const compoundlteq = `(${this.registerCompoundLTEQ(lhvtype, rhvtype)} ${larg} ${rarg})`;
                        return `${this.varToCppName(bcmp.trgt)} = ${compoundlteq};`;
                    }
                    else {
                        const compoundlteq = `(${this.registerCompoundLTEQ(lhvtype, rhvtype)} ${rarg} ${larg})`;
                        return `${this.varToCppName(bcmp.trgt)} = ${compoundlteq};`;
                    }
                }
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
                return `${this.varToCppName(top.trgt)} = ${this.generateTypeCheck(this.argToCpp(top.arg, this.getArgType(top.arg)), this.getArgType(top.arg), this.typegen.getMIRType(top.oftype), true)};`;
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
                    return `printf("%s\\n", Runtime::diagnostic_format(${this.argToCpp(dbgop.value, this.typegen.anyType)}).c_str());`;
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
            const cslotvar = this.varNameToCppName("$callerslot$");
            if (this.typegen.maybeRefableCountableType(this.currentRType)) {
                if (!this.assembly.subtypeOf(this.typegen.boolType, this.currentRType) && !this.assembly.subtypeOf(this.typegen.intType, this.currentRType)) {
                    if (this.assembly.subtypeOf(this.typegen.noneType, this.currentRType)) {
                        gblock.push(`BSQRefScopeMgr::processCallRefNoneable(${cslotvar}, _return_);`);
                    }
                    else {
                        gblock.push(`BSQRefScopeMgr::processCallReturnFast(${cslotvar}, _return_);`);
                    }
                }
                else {
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
        if (vdecls.has("int64_t")) {
            vdeclscpp.push(`int64_t ${(vdecls.get("int64_t") as string[]).join(", ")};`);
        }
        [...vdecls].sort((a, b) => a[0].localeCompare(b[0])).forEach((kv) => {
            if (kv[0] !== "bool" && kv[0] !== "int64_t") {
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
            const cslotvar = this.varNameToCppName("$callerslot$");
            args.push(`BSQRef** ${cslotvar}`);
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
                    return lbl + stmts;
                });

                const scopestrs = this.generateCPPVarDecls(idecl.body, idecl.params);

                return { fwddecl: decl + ";", fulldecl: `${decl}\n{\n${scopestrs}\n\n${blockstrs.join("\n\n")}\n}\n` };
            }
            else {
                let prestr = ";";
                const preargs = idecl.params.map((arg) => this.varNameToCppName(arg.name));

                let poststr = "   return _return_;";
                const postargs = [...idecl.params.map((arg) => this.varNameToCppName(arg.name)), "_return_"];

                if(idecl.preconditions.length !== 0) {
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
                    return lbl + stmts.join("\n");
                });

                const scopestrs = this.generateCPPVarDecls(idecl.body, idecl.params);

                return { fwddecl: decl + ";", fulldecl: `${decl}\n{\n${prestr}\n${scopestrs}\n\n${blockstrs.join("\n\n")}\n}\n` };
            }
        }
        else {
            assert(idecl instanceof MIRInvokePrimitiveDecl);

            const params = idecl.params.map((arg) => this.varNameToCppName(arg.name));
            if (this.typegen.maybeRefableCountableType(this.typegen.getMIRType(idecl.resultType))) {
                const cslotvar = this.varNameToCppName("$callerslot$");
                params.push(cslotvar);
            }

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
                return lbl + stmts;
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
                return lbl + stmts;
            });

            const decl = `bool ${this.invokenameToCPP(postkey)}${i}(${args.join(", ")})`;
            const scopestrs = this.generateCPPVarDecls(pc, idecl.params);

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
                return lbl + stmts;
            });

            const decl = `bool ${this.invokenameToCPP(invkey)}${i}(${this.typegen.typeToCPPType(this.typegen.getMIRType(idecl.tkey), "parameter")} ${this.typegen.mangleStringForCpp("this")})`;
            const scopestrs = this.generateCPPVarDecls(idecl.invariants[0], [new MIRFunctionParameter(this.typegen.mangleStringForCpp("this"), idecl.tkey)]);

            return [`${decl}\n{\n${scopestrs}\n\n${blockstrs.join("\n\n")}\n}\n`, `${this.invokenameToCPP(invkey)}${i}(${this.typegen.mangleStringForCpp("this")})`];
        });

        const declroot = `void ${this.invokenameToCPP(invkey)}(${this.typegen.typeToCPPType(this.typegen.getMIRType(idecl.tkey), "parameter")} ${this.typegen.mangleStringForCpp("this")})`;
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
        const cslotvar = this.varNameToCppName("$callerslot$");
        const gdecl = `bool ${flagname} = false; ${decltype} ${memoname};`;
        const qcheck = `    if (${flagname}) { return ${memoname}; }\n    ${this.typegen.maybeRefableCountableType(this.typegen.getMIRType(cdecl.declaredType)) ? "BSQRef* $callerslot_dummy$ = nullptr; BSQRef** " + cslotvar + " = &$callerslot_dummy$;" : ""}`;
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
            return lbl + stmts;
        });

        const scopestrs = this.generateCPPVarDecls(cdecl.value, []);
        const jblockstrs = blockstrs.join("\n\n");

        const rstart = jblockstrs.indexOf("return _return_");
        const nblockstrs = jblockstrs.slice(0, rstart) + rupdate + "\n    " + jblockstrs.slice(rstart);

        return { fwddecl: decl + ";", fulldecl: `${gdecl}\n${decl}\n{\n${scopestrs}\n\n${qcheck}\n\n${nblockstrs}\n}\n` };
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
        const cslotvar = this.varNameToCppName("$callerslot$");
        const gdecl = `bool ${flagname} = false; ${decltype}; ${memoname};`;
        const qcheck = `    if (${flagname}) { return ${memoname}; }\n    ${this.typegen.maybeRefableCountableType(this.typegen.getMIRType(fdecl.declaredType)) ? "BSQRef* $callerslot_dummy$ = nullptr; BSQRef** " + cslotvar + " = &$callerslot_dummy$;" : ""}`;
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
            return lbl + stmts;
        });

        const scopestrs = this.generateCPPVarDecls(fdbody, []);
        const jblockstrs = blockstrs.join("\n\n");

        const rstart = jblockstrs.indexOf("return _return_;");
        const nblockstrs = jblockstrs.slice(0, rstart) + rupdate + "\n    " + jblockstrs.slice(rstart);

        return { fwddecl: decl + ";", fulldecl: `${gdecl}\n${decl}\n{\n${scopestrs}\n\n${qcheck}\n\n${nblockstrs}\n}\n` };
    }

    generateBuiltinBody(idecl: MIRInvokePrimitiveDecl, params: string[]): string {
        switch (idecl.implkey) {
            case "_listcons": {
                const lentity = this.assembly.entityDecls.get((this.typegen.getMIRType(idecl.resultType).options[0] as MIREntityType).ekey) as MIREntityTypeDecl;
                const clisttype = this.typegen.getMIRType((lentity.fields.find((fd) => fd.name === "list") as MIRFieldDecl).declaredType);
                const smtctype = this.typegen.typeToCPPType(this.typegen.getMIRType(idecl.resultType), "base");

                return `auto res = new ${smtctype}(BSQRef::checkedIncrementNoneable<${this.typegen.typeToCPPType(clisttype, "base")}>(${params[1]}), ${params[0]}); BSQRefScopeMgr::processCallReturnFast(${params[2]}, res); return res;`;
            }
            case "_setcons": {
                const sentity = this.assembly.entityDecls.get((this.typegen.getMIRType(idecl.resultType).options[0] as MIREntityType).ekey) as MIREntityTypeDecl;
                const csettype = this.typegen.getMIRType((sentity.fields.find((fd) => fd.name === "set") as MIRFieldDecl).declaredType);
                const smtctype = this.typegen.typeToCPPType(this.typegen.getMIRType(idecl.resultType), "base");

                return `auto res = new ${smtctype}(BSQRef::checkedIncrementNoneable<${this.typegen.typeToCPPType(csettype, "base")}>(${params[1]}), ${params[0]}); BSQRefScopeMgr::processCallReturnFast(${params[2]}, res); return res;`;
            }
            case "_mapcons": {
                const mentity = this.assembly.entityDecls.get((this.typegen.getMIRType(idecl.resultType).options[0] as MIREntityType).ekey) as MIREntityTypeDecl;
                const cmaptype = this.typegen.getMIRType((mentity.fields.find((fd) => fd.name === "map") as MIRFieldDecl).declaredType);
                const smtctype = this.typegen.typeToCPPType(this.typegen.getMIRType(idecl.resultType), "base");

                return `auto res = new ${smtctype}(BSQRef::checkedIncrementNoneable<${this.typegen.typeToCPPType(cmaptype, "base")}>(${params[1]}), ${params[0]}); BSQRefScopeMgr::processCallReturnFast(${params[2]}, res); return res;`;
            }
            default: {
                return (CoreImplBodyText.get(idecl.implkey) as ((params: string[]) => string))(params);
            }
        }
    }
}

export {
    CPPBodyEmitter
};
