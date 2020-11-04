//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { SourceInfo } from "../ast/parser";
import { topologicalOrder, computeBlockLinks, FlowLink } from "./mir_info";
import { BSQRegex } from "../ast/bsqregex";

import assert = require("assert");
import { MIRType } from "./mir_assembly";

type MIRGlobalKey = string; //$global_IKEY
type MIRFieldKey = string; //ns::name::field#binds
type MIRInvokeKey = string; //ns::[type]::func#binds%code

type MIRResolvedTypeKey = string; //idstr
type MIRVirtualMethodKey = string; //method#binds

//
//Probably want to declare a MIRSourceInfo class
//
function jemitsinfo(sinfo: SourceInfo): object {
    return { line: sinfo.line, column: sinfo.column, pos: sinfo.pos, span: sinfo.span };
}

function jparsesinfo(jobj: any): SourceInfo {
    return new SourceInfo(jobj.line, jobj.column, jobj.pos, jobj.span);
}

abstract class MIRArgument {
    readonly nameID: string;

    constructor(nameID: string) {
        this.nameID = nameID;
    }

    abstract stringify(): string;

    abstract jemit(): object;

    static jparse(jobj: any): MIRArgument {
        if(jobj === null) {
            return new MIRConstantNone;
        }
        else if(typeof(jobj) === "boolean") {
            return jobj ? new MIRConstantTrue() : new MIRConstantFalse();
        }
        else if(typeof(jobj) === "string") {
            return new MIRConstantString(jobj);
        }
        else {
            const ckind = jobj.constkind;
            switch(ckind) {
                case "int":
                    return new MIRConstantInt(jobj.value);
                case "nat":
                    return new MIRConstantNat(jobj.value);
                case "bigint":
                    return new MIRConstantBigInt(jobj.value);
                case "bignat":
                    return new MIRConstantBigNat(jobj.value);
                case "rational":
                    return new MIRConstantRational(jobj.value);
                case "complex":
                    return new MIRConstantComplex(jobj.rvalue, jobj.cvalue);
                case "float":
                    return new MIRConstantFloat(jobj.value);
                case "decimal":
                    return new MIRConstantDecmial(jobj.value);
                case "regex":
                    return new MIRConstantRegex(jobj.value);
                default:
                    return new MIRConstantStringOf(jobj.value, jobj.oftype);
            }
        }
    }
}

abstract class MIRRegisterArgument extends MIRArgument {
    constructor(nameID: string) {
        super(nameID);
    }

    stringify(): string {
        return this.nameID;
    }
}

class MIRTempRegister extends MIRRegisterArgument {
    readonly regID: number;
    constructor(regID: number, forcename?: string) {
        super(forcename || `#tmp_${regID}`);
        this.regID = regID;
    }

    jemit(): object {
        return { tag: "temp", regID: this.regID, nameID: this.nameID };
    }

    static jparse(jobj: any): MIRTempRegister {
        return new MIRTempRegister(jobj.regID, jobj.nameID);
    }
}

class MIRGlobalVariable extends MIRRegisterArgument {
    constructor(gkey: MIRGlobalKey) {
        super(gkey);
    }

    jemit(): object {
        return { tag: "global", gkey: this.nameID };
    }

    static jparse(jobj: any): MIRGlobalVariable {
        return new MIRGlobalVariable(jobj.gkey);
    }
}

abstract class MIRVariableArgument extends MIRRegisterArgument {
    readonly lname: string;

    constructor(name: string, forcename: string | undefined) {
        super(forcename || name);
        this.lname = name;
    }
}

class MIRParameterVariable extends MIRVariableArgument {
    constructor(name: string, forcename?: string) {
        super(name, forcename);
    }

    jemit(): any {
        return { tag: "paramvar", lname: this.lname, nameID: this.nameID };
    }

    static jparse(jobj: any): MIRParameterVariable {
        return new MIRParameterVariable(jobj.lname, jobj.nameID);
    }
}

class MIRLocalVariable extends MIRVariableArgument {
    constructor(name: string, forcename?: string) {
        super(name, forcename);
    }

    jemit(): any {
        return { tag: "localvar", lname: this.lname, nameID: this.nameID };
    }

    static jparse(jobj: any): MIRLocalVariable {
        return new MIRLocalVariable(jobj.lname, jobj.nameID);
    }
}

abstract class MIRConstantArgument extends MIRArgument {
    constructor(name: string) {
        super(name);
    }
}

class MIRConstantNone extends MIRConstantArgument {
    constructor() {
        super("=none=");
    }

    stringify(): string {
        return "none";
    }

    jemit(): any {
        return null;
    }
}

class MIRConstantTrue extends MIRConstantArgument {
    constructor() {
        super("=true=");
    }

    stringify(): string {
        return "true";
    }

    jemit(): any {
        return true;
    }
}

class MIRConstantFalse extends MIRConstantArgument {
    constructor() {
        super("=false=");
    }

    stringify(): string {
        return "false";
    }

    jemit(): any {
        return false;
    }
}

class MIRConstantInt extends MIRConstantArgument {
    readonly value: string;

    constructor(value: string) {
        super(`=int=${value}`);

        this.value = value;
    }

    stringify(): string {
        return this.value;
    }

    jemit(): any {
        return { constkind: "int", value: this.value };
    }
}

class MIRConstantNat extends MIRConstantArgument {
    readonly value: string;

    constructor(value: string) {
        super(`=nat=${value}`);

        this.value = value;
    }

    stringify(): string {
        return this.value;
    }

    jemit(): any {
        return { constkind: "nat", value: this.value };
    }
}

class MIRConstantBigInt extends MIRConstantArgument {
    readonly value: string;

    constructor(value: string) {
        super(`=bigint=${value}`);

        this.value = value;
    }

    digits(): string {
        return this.value.slice(0, this.value.length - 1);
    }

    stringify(): string {
        return this.value;
    }

    jemit(): any {
        return { constkind: "bigint", value: this.value };
    }
}

class MIRConstantBigNat extends MIRConstantArgument {
    readonly value: string;

    constructor(value: string) {
        super(`=bignat=${value}`);

        this.value = value;
    }

    digits(): string {
        return this.value.slice(0, this.value.length - 1);
    }

    stringify(): string {
        return this.value;
    }

    jemit(): any {
        return { constkind: "bignat", value: this.value };
    }
}

class MIRConstantRational extends MIRConstantArgument {
    readonly value: string;

    constructor(value: string) {
        super(`=rational=${value}`);

        this.value = value;
    }

    stringify(): string {
        return this.value;
    }

    jemit(): any {
        return { constkind: "rational", value: this.value };
    }
}

class MIRConstantComplex extends MIRConstantArgument {
    readonly rvalue: string;
    readonly ivalue: string;

    constructor(rvalue: string, ivalue: string) {
        super(`=complex=${rvalue}${ivalue}`);

        this.rvalue = rvalue;
        this.ivalue = ivalue;
    }

    stringify(): string {
        return `${this.rvalue}${this.ivalue}`;
    }

    jemit(): any {
        return { constkind: "complex", rvalue: this.rvalue, cvalue: this.ivalue };
    }
}

class MIRConstantFloat extends MIRConstantArgument {
    readonly value: string;

    constructor(value: string) {
        super(`=float=${value}`);

        this.value = value;
    }

    digits(): string {
        return this.value.slice(0, this.value.length - 1);
    }
    
    stringify(): string {
        return this.value;
    }

    jemit(): any {
        return { constkind: "float", value: this.value };
    }
}

class MIRConstantDecmial extends MIRConstantArgument {
    readonly value: string;

    constructor(value: string) {
        super(`=decimal=${value}`);

        this.value = value;
    }

    digits(): string {
        return this.value.slice(0, this.value.length - 1);
    }
    
    stringify(): string {
        return this.value;
    }

    jemit(): any {
        return { constkind: "decimal", value: this.value };
    }
}

class MIRConstantString extends MIRConstantArgument {
    readonly value: string;

    constructor(value: string) {
        super(`=string=${value}`);

        this.value = value;
    }

    stringify(): string {
        return this.value;
    }

    jemit(): any {
        return this.value;
    }
}

class MIRConstantRegex extends MIRConstantArgument {
    readonly value: BSQRegex;

    constructor(value: BSQRegex) {
        super(`=regex=${value.restr}`);

        this.value = value;
    }

    stringify(): string {
        return this.value.restr;
    }

    jemit(): any {
        return { constkind: "regex", value: this.value.jemit() };
    }
}

class MIRConstantStringOf extends MIRConstantArgument {
    readonly value: string;
    readonly tskey: MIRResolvedTypeKey;

    constructor(value: string, tskey: MIRResolvedTypeKey) {
        super(`=stringof=${tskey} of ${value}`);

        this.value = value;
        this.tskey = tskey;
    }

    stringify(): string {
        return `${this.tskey} of ${this.value}`;
    }

    jemit(): any {
        return { constkind: "stringof", value: this.value, oftype: this.tskey };
    }
}

enum MIROpTag {
    MIRNop = "MIRNop",
    MIRDeadFlow = "MIRDeadFlow",
    MIRLoadConst = "MIRLoadConst",
    MIRLoadConstDataString = "MIRLoadConstDataString",

    MIRTupleHasIndex = "MIRTupleHasIndex",
    MIRRecordHasProperty = "MIRRecordHasProperty",
    MIRLoadTupleIndex = "MIRLoadTupleIndex",
    MIRCheckedLoadTupleIndex = "MIRCheckedLoadTupleIndex",
    MIRLoadTupleIndexTry = "MIRLoadTupleIndexTry",
    MIRLoadRecordProperty = "MIRLoadRecordProperty",
    MIRCheckedLoadRecordProperty = "MIRCheckedLoadRecordProperty",
    MIRLoadRecordPropertyTry = "MIRLoadRecordPropertyTry",

    MIRLoadField = "MIRLoadField",

    MIRLoadFromEpehmeralList = "MIRLoadFromEpehmeralList",
    MIRMultiLoadFromEpehmeralList = "MIRMultiLoadFromEpehmeralList",

    MIRTempRegisterAssign = "MIRTempRegisterAssign",
    MIRParameterVarStore = "MIRParameterVarStore",
    MIRLocalVarStore = "MIRParameterVarStore",
    MIRParameterVarStoreWithGuard = "MIRParameterVarStoreWithGuard",
    MIRLocalVarStoreWithGuard = "MIRLocalVarStoreWithGuard"
}

function varsOnlyHelper(args: MIRArgument[]): MIRRegisterArgument[] {
    return args.filter((arg) => arg instanceof MIRRegisterArgument) as MIRRegisterArgument[];
}

abstract class MIROp {
    readonly tag: MIROpTag;
    readonly sinfo: SourceInfo;

    constructor(tag: MIROpTag, sinfo: SourceInfo) {
        this.tag = tag;
        this.sinfo = sinfo;
    }

    abstract getUsedVars(): MIRRegisterArgument[];
    abstract getModVars(): MIRRegisterArgument[];

    abstract stringify(): string;

    protected jbemit(): object {
        return { tag: this.tag, sinfo: jemitsinfo(this.sinfo) };
    }

    abstract jemit(): object;

    static jparse(jobj: any & { tag: string }): MIROp {
        switch (jobj.tag) {
            case MIROpTag.MIRLoadConst:
                return MIRLoadConst.jparse(jobj);
            case MIROpTag.MIRLoadConstSafeString:
                return MIRLoadConstSafeString.jparse(jobj);
            case MIROpTag.MIRLoadConstTypedString:
                return MIRLoadConstTypedString.jparse(jobj);
            case MIROpTag.MIRAccessConstantValue:
                return MIRAccessConstantValue.jparse(jobj);
            case MIROpTag.MIRLoadFieldDefaultValue:
                return MIRLoadFieldDefaultValue.jparse(jobj);
            case MIROpTag.MIRInvokeInvariantCheckDirect:
                return MIRInvokeInvariantCheckDirect.jparse(jobj);
            case MIROpTag.MIRInvokeInvariantCheckVirtualTarget:
                return MIRInvokeInvariantCheckVirtualTarget.jparse(jobj);
            case MIROpTag.MIRConstructorPrimary:
                return MIRConstructorPrimary.jparse(jobj);
            case MIROpTag.MIRConstructorPrimaryCollectionEmpty:
                return MIRConstructorPrimaryCollectionEmpty.jparse(jobj);
            case MIROpTag.MIRConstructorPrimaryCollectionSingletons:
                return MIRConstructorPrimaryCollectionSingletons.jparse(jobj);
            case MIROpTag.MIRConstructorPrimaryCollectionCopies:
                return MIRConstructorPrimaryCollectionCopies.jparse(jobj);
            case MIROpTag.MIRConstructorPrimaryCollectionMixed:
                return MIRConstructorPrimaryCollectionMixed.jparse(jobj);
            case MIROpTag.MIRConstructorTuple:
                return MIRConstructorTuple.jparse(jobj);
            case MIROpTag.MIRConstructorRecord:
                return MIRConstructorRecord.jparse(jobj);
            case MIROpTag.MIRConstructorEphemeralValueList:
                return MIRConstructorEphemeralValueList.jparse(jobj);
            case MIROpTag.MIRAccessFromIndex:
                return MIRAccessFromIndex.jparse(jobj);
            case MIROpTag.MIRProjectFromIndecies:
                return MIRProjectFromIndecies.jparse(jobj);
            case MIROpTag.MIRAccessFromProperty:
                return MIRAccessFromProperty.jparse(jobj);
            case MIROpTag.MIRProjectFromProperties:
                return MIRProjectFromProperties.jparse(jobj);
            case MIROpTag.MIRAccessFromField:
                return MIRAccessFromField.jparse(jobj);
            case MIROpTag.MIRProjectFromFields:
                return MIRProjectFromFields.jparse(jobj);
            case MIROpTag.MIRProjectFromTypeTuple:
                return MIRProjectFromTypeTuple.jparse(jobj);
            case MIROpTag.MIRProjectFromTypeRecord:
                return MIRProjectFromTypeRecord.jparse(jobj);
            case MIROpTag.MIRProjectFromTypeNominal:
                return MIRProjectFromTypeNominal.jparse(jobj);
            case MIROpTag.MIRModifyWithIndecies:
                return MIRModifyWithIndecies.jparse(jobj);
            case MIROpTag.MIRModifyWithProperties:
                return MIRModifyWithProperties.jparse(jobj);
            case MIROpTag.MIRModifyWithFields:
                return MIRModifyWithFields.jparse(jobj);
            case MIROpTag.MIRStructuredExtendTuple:
                return MIRStructuredExtendTuple.jparse(jobj);
            case MIROpTag.MIRStructuredExtendRecord:
                return MIRStructuredExtendRecord.jparse(jobj);
            case MIROpTag.MIRStructuredExtendObject:
                return MIRStructuredExtendObject.jparse(jobj);
            case MIROpTag.MIRLoadFromEpehmeralList:
                return MIRLoadFromEpehmeralList.jparse(jobj);
            case MIROpTag.MIRInvokeFixedFunction:
                return MIRInvokeFixedFunction.jparse(jobj);
            case MIROpTag.MIRInvokeVirtualTarget:
                return MIRInvokeVirtualFunction.jparse(jobj);
            case MIROpTag.MIRPrefixOp:
                return MIRPrefixOp.jparse(jobj);
            case MIROpTag.MIRBinOp:
                return MIRBinOp.jparse(jobj);
            case MIROpTag.MIRBinEq:
                return MIRBinEq.jparse(jobj);
            case MIROpTag.MIRBinLess:
                return MIRBinLess.jparse(jobj);
            case MIROpTag.MIRBinCmp:
                return MIRBinCmp.jparse(jobj);
            case MIROpTag.MIRIsTypeOfNone:
                return MIRIsTypeOfNone.jparse(jobj);
            case MIROpTag.MIRIsTypeOfSome:
                return MIRIsTypeOfSome.jparse(jobj);
            case MIROpTag.MIRIsTypeOf:
                return MIRIsTypeOf.jparse(jobj);
            case MIROpTag.MIRRegAssign:
                return MIRRegAssign.jparse(jobj);
            case MIROpTag.MIRTruthyConvert:
                return MIRTruthyConvert.jparse(jobj);
            case MIROpTag.MIRVarStore:
                return MIRVarStore.jparse(jobj);
            case MIROpTag.MIRPackSlice:
                return MIRPackSlice.jparse(jobj);
            case MIROpTag.MIRPackExtend:
                return MIRPackExtend.jparse(jobj);
            case MIROpTag.MIRReturnAssign:
                return MIRReturnAssign.jparse(jobj);
            case MIROpTag.MIRAbort:
                return MIRAbort.jparse(jobj);
            case MIROpTag.MIRDebug:
                return MIRDebug.jparse(jobj);
            case MIROpTag.MIRJump:
                return MIRJump.jparse(jobj);
            case MIROpTag.MIRJumpCond:
                return MIRJumpCond.jparse(jobj);
            case MIROpTag.MIRJumpNone:
                return MIRJumpNone.jparse(jobj);
            case MIROpTag.MIRPhi:
                return MIRPhi.jparse(jobj);
            case MIROpTag.MIRVarLifetimeStart:
                return MIRVarLifetimeStart.jparse(jobj);
            default:
                assert(jobj.tag === MIROpTag.MIRVarLifetimeEnd);
                return MIRVarLifetimeEnd.jparse(jobj);
        }
    }
}

class MIRNop extends MIROp {
    constructor(sinfo: SourceInfo) {
        super(MIROpTag.MIRNop, sinfo);
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `nop`;
    }

    jemit(): object {
        return { ...this.jbemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRNop(jparsesinfo(jobj.sinfo));
    }
}

class MIRDeadFlow extends MIROp {
    constructor(sinfo: SourceInfo) {
        super(MIROpTag.MIRDeadFlow, sinfo); 
     }
 
     getUsedVars(): MIRRegisterArgument[] { return []; }
     getModVars(): MIRRegisterArgument[] { return []; }
 
     stringify(): string {
         return `dead-flow`;
     }
 
     jemit(): object {
         return { ...this.jbemit() };
     }
 
     static jparse(jobj: any): MIROp {
         return new MIRNop(jparsesinfo(jobj.sinfo));
     }
 }

abstract class MIRValueOp extends MIROp {
    trgt: MIRTempRegister;

    constructor(tag: MIROpTag, sinfo: SourceInfo, trgt: MIRTempRegister) {
        super(tag, sinfo);
        this.trgt = trgt;
    }

    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    protected jbemit(): object {
        return {...super.jbemit(), trgt: this.trgt.jemit() };
    }
}

abstract class MIRFlowOp extends MIROp {
    constructor(tag: MIROpTag, sinfo: SourceInfo) {
        super(tag, sinfo);
    }
}

abstract class MIRJumpOp extends MIROp {
    constructor(tag: MIROpTag, sinfo: SourceInfo) {
        super(tag, sinfo);
    }
}

class MIRLoadConst extends MIRValueOp {
    readonly src: MIRConstantArgument;

    constructor(sinfo: SourceInfo, src: MIRConstantArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRLoadConst, sinfo, trgt);
        this.src = src;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.src.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), src: this.src.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLoadConst(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src) as MIRConstantArgument, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRLoadConstDataString extends MIRValueOp {
    readonly ivalue: string;
    readonly tskey: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, ivalue: string, tskey: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRLoadConstDataString, sinfo, trgt);
        this.ivalue = ivalue;
        this.tskey = tskey;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.tskey}${this.ivalue}`;
    }

    jemit(): object {
        return { ...this.jbemit(), ivalue: this.ivalue, tskey: this.tskey };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLoadConstDataString(jparsesinfo(jobj.sinfo), jobj.ivalue, jobj.tskey, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRTupleHasIndex extends MIRValueOp {
    arg: MIRArgument;
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    readonly idx: number;
    readonly isvirtual: boolean;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, idx: number, isvirtual: boolean, trgt: MIRTempRegister) {
        super(MIROpTag.MIRTupleHasIndex, sinfo, trgt);

        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.idx = idx;
        this.isvirtual = isvirtual;
    }
    
    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.hasIndex<${this.idx}>()`;
    }

    jemit(): object {
        return { ...this.jbemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, idx: this.idx, isvirtual: this.isvirtual };
    }

    static jparse(jobj: any): MIROp {
        return new MIRTupleHasIndex(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, jobj.idx, jobj.isvirtual, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRRecordHasProperty extends MIRValueOp {
    arg: MIRArgument;
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    readonly pname: string;
    readonly isvirtual: boolean;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, pname: string, isvirtual: boolean, trgt: MIRTempRegister) {
        super(MIROpTag.MIRRecordHasProperty, sinfo, trgt);

        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.pname = pname;
        this.isvirtual = isvirtual;
    }
    
    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.hasProperty<${this.pname}>()`;
    }

    jemit(): object {
        return { ...this.jbemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, pname: this.pname, isvirtual: this.isvirtual };
    }

    static jparse(jobj: any): MIROp {
        return new MIRRecordHasProperty(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, jobj.pname, jobj.isvirtual, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRLoadTupleIndex extends MIRValueOp {
    arg: MIRArgument;
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    readonly idx: number;
    readonly isvirtual: boolean;
    readonly resulttype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, idx: number, isvirtual: boolean, resulttype: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRLoadTupleIndex, sinfo, trgt);
        
        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.idx = idx;
        this.isvirtual = isvirtual;
        this.resulttype = resulttype;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.${this.idx}`;
    }

    jemit(): object {
        return { ...this.jbemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, idx: this.idx, isvirtual: this.isvirtual, resulttype: this.resulttype };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLoadTupleIndex(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, jobj.idx, jobj.isvirtual, jobj.resulttype, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRCheckedLoadTupleIndex extends MIRValueOp {
    arg: MIRArgument;
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    readonly idx: number;
    readonly isvirtual: boolean; 
    readonly resulttype: MIRResolvedTypeKey;
    readonly mask: string;
    readonly position: number;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, idx: number, isvirtual: boolean, resulttype: MIRResolvedTypeKey, trgt: MIRTempRegister, mask: string, position: number) {
        super(MIROpTag.MIRCheckedLoadTupleIndex, sinfo, trgt);

        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.idx = idx;
        this.isvirtual = isvirtual;
        this.resulttype = resulttype;
        this.mask = mask;
        this.position = position;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.${this.idx} | ${this.mask}[${this.position}]`;
    }

    jemit(): object {
        return { ...this.jbemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, idx: this.idx, isvirtual: this.isvirtual, resulttype: this.resulttype, mask: this.mask, position: this.position };
    }

    static jparse(jobj: any): MIROp {
        return new MIRCheckedLoadTupleIndex(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, jobj.idx, jobj.isvirtual, jobj.resulttype, MIRTempRegister.jparse(jobj.trgt), jobj.mask, jobj.position);
    }
}

class MIRLoadTupleIndexTry extends MIRFlowOp {
    arg: MIRArgument;
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    readonly idx: number;
    readonly isvirtual: boolean;
    readonly resulttype: MIRResolvedTypeKey;
    trgt: MIRRegisterArgument;
    hastrgt: MIRTempRegister;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, idx: number, isvirtual: boolean, resulttype: MIRResolvedTypeKey, trgt: MIRRegisterArgument, hastrgt: MIRTempRegister) {
        super(MIROpTag.MIRLoadTupleIndexTry, sinfo);

        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.idx = idx;
        this.isvirtual = isvirtual;
        this.resulttype = resulttype;
        this.trgt = trgt;
        this.hastrgt = hastrgt;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt, this.hastrgt]; }

    stringify(): string {
        return `${this.hastrgt.stringify()} = ${this.arg.stringify()}.getIndexTry<${this.idx}>(out? ${this.trgt.stringify()})`;
    }

    jemit(): object {
        return { ...this.jbemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, idx: this.idx, isvirtual: this.isvirtual, resulttype: this.resulttype, trgt: this.trgt.jemit(), hastrgt: this.hastrgt.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLoadTupleIndexTry(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, jobj.idx, jobj.isvirtual, jobj.resulttype, MIRRegisterArgument.jparse(jobj.trgt), MIRTempRegister.jparse(jobj.hastrgt));
    }
}

class MIRLoadRecordProperty extends MIRValueOp {
    arg: MIRArgument;
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    readonly pname: string;
    readonly isvirtual: boolean;
    readonly resulttype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, pname: string, isvirtual: boolean, resulttype: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRLoadRecordProperty, sinfo, trgt);
        
        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.pname = pname;
        this.isvirtual = isvirtual;
        this.resulttype = resulttype;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.${this.pname}`;
    }

    jemit(): object {
        return { ...this.jbemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, pname: this.pname, isvirtual: this.isvirtual, resulttype: this.resulttype };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLoadRecordProperty(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, jobj.pname, jobj.isvirtual, jobj.resulttype, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRCheckedLoadRecordProperty extends MIRValueOp {
    arg: MIRArgument;
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    readonly pname: string;
    readonly isvirtual: boolean; 
    readonly resulttype: MIRResolvedTypeKey;
    readonly mask: string;
    readonly position: number;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, pname: string, isvirtual: boolean, resulttype: MIRResolvedTypeKey, trgt: MIRTempRegister, mask: string, position: number) {
        super(MIROpTag.MIRCheckedLoadRecordProperty, sinfo, trgt);

        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.pname = pname;
        this.isvirtual = isvirtual;
        this.resulttype = resulttype;
        this.mask = mask;
        this.position = position;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.${this.pname} | ${this.mask}[${this.position}]`;
    }

    jemit(): object {
        return { ...this.jbemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, pname: this.pname, isvirtual: this.isvirtual, resulttype: this.resulttype, mask: this.mask, position: this.position };
    }

    static jparse(jobj: any): MIROp {
        return new MIRCheckedLoadRecordProperty(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, jobj.pname, jobj.isvirtual, jobj.resulttype, MIRTempRegister.jparse(jobj.trgt), jobj.mask, jobj.position);
    }
}

class MIRLoadRecordPropertyTry extends MIRFlowOp {
    arg: MIRArgument;
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    readonly pname: string;
    readonly isvirtual: boolean;
    readonly resulttype: MIRResolvedTypeKey;
    trgt: MIRRegisterArgument;
    hastrgt: MIRTempRegister;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, pname: string, isvirtual: boolean, resulttype: MIRResolvedTypeKey, trgt: MIRRegisterArgument, hastrgt: MIRTempRegister) {
        super(MIROpTag.MIRLoadRecordPropertyTry, sinfo);

        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.pname = pname;
        this.isvirtual = isvirtual;
        this.resulttype = resulttype;
        this.trgt = trgt;
        this.hastrgt = hastrgt;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt, this.hastrgt]; }

    stringify(): string {
        return `${this.hastrgt.stringify()} = ${this.arg.stringify()}.getPropertyTry<${this.pname}>(out? ${this.trgt.stringify()})`;
    }

    jemit(): object {
        return { ...this.jbemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, pname: this.pname, isvirtual: this.isvirtual, resulttype: this.resulttype, trgt: this.trgt.jemit(), hastrgt: this.hastrgt.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLoadRecordPropertyTry(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, jobj.pname, jobj.isvirtual, jobj.resulttype, MIRRegisterArgument.jparse(jobj.trgt), MIRTempRegister.jparse(jobj.hastrgt));
    }
}

class MIRLoadField extends MIRValueOp {
    arg: MIRArgument;
    readonly arglayouttype: MIRResolvedTypeKey;
    readonly argflowtype: MIRResolvedTypeKey;
    readonly field: MIRFieldKey;
    readonly isvirtual: boolean;
    readonly resulttype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, field: MIRFieldKey, isvirtual: boolean, resulttype: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRLoadField, sinfo, trgt);

        this.arg = arg;
        this.arglayouttype = arglayouttype;
        this.argflowtype = argflowtype;
        this.field = field;
        this.isvirtual = isvirtual;
        this.resulttype = resulttype;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}.${this.field}`;
    }

    jemit(): object {
        return { ...this.jbemit(), arg: this.arg.jemit(), arglayouttype: this.arglayouttype, argflowtype: this.argflowtype, field: this.field, isvirtual: this.isvirtual, resulttype: this.resulttype };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLoadField(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.arglayouttype, jobj.argflowtype, jobj.field, jobj.isvirtual, jobj.resulttype, MIRTempRegister.jparse(jobj.trgt));
    }
}


class MIRLoadFromEpehmeralList extends MIRValueOp {
    arg: MIRArgument;
    readonly argtype: MIRType;
    readonly idx: number;
    readonly resulttype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRType, idx: number, resulttype: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRLoadFromEpehmeralList, sinfo, trgt);

        this.arg = arg;
        this.argtype = argtype;
        this.idx = idx;
        this.resulttype = resulttype;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}(|${this.idx}|)`;
    }

    jemit(): object {
        return { ...this.jbemit(), arg: this.arg.jemit(), argtype: this.argtype, idx: this.idx, resulttype: this.resulttype };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLoadFromEpehmeralList(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.argtype, jobj.idx, jobj.resulttype, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRMultiLoadFromEpehmeralList extends MIRFlowOp {
    arg: MIRRegisterArgument;
    readonly argtype: MIRResolvedTypeKey;
    trgts: { pos: number, into: MIRRegisterArgument, oftype: MIRType }[];

    constructor(sinfo: SourceInfo, arg: MIRRegisterArgument, resultType: MIRResolvedTypeKey, argInferType: MIRResolvedTypeKey, idx: number, trgt: MIRTempRegister) {
        super(MIROpTag.MIRMultiLoadFromEpehmeralList, sinfo);
        this.arg = arg;
        this.resultType = resultType;
        this.argInferType = argInferType;
        this.idx = idx;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.arg.stringify()}(|${this.idx}|)`;
    }

    jemit(): object {
        return { ...this.jbemit(), arg: this.arg.jemit(), resultType: this.resultType, argInferType: this.argInferType, idx: this.idx };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLoadFromEpehmeralList(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg) as MIRRegisterArgument, jobj.resultType, jobj.argInferType, jobj.idx, MIRTempRegister.jparse(jobj.trgt));
    }
}





class MIRConstructorPrimary extends MIRValueOp {
    readonly tkey: MIRNominalTypeKey;
    args: MIRArgument[];

    constructor(sinfo: SourceInfo, tkey: MIRNominalTypeKey, args: MIRArgument[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRConstructorPrimary, sinfo, trgt);
        this.tkey = tkey;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.tkey}@(${this.args.map((arg) => arg.stringify()).join(", ")})`;
    }

    jemit(): object {
        return { ...this.jbemit(), tkey: this.tkey, args: this.args.map((arg) => arg.jemit()) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorPrimary(jparsesinfo(jobj.sinfo), jobj.tkey, jobj.args.map((jarg: any) => MIRArgument.jparse(jarg)), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRConstructorPrimaryCollectionEmpty extends MIRValueOp {
    readonly tkey: MIRNominalTypeKey;

    constructor(sinfo: SourceInfo, tkey: MIRNominalTypeKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRConstructorPrimaryCollectionEmpty, sinfo, trgt);
        this.tkey = tkey;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.tkey}{}`;
    }

    jemit(): object {
        return { ...this.jbemit(), tkey: this.tkey };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorPrimaryCollectionEmpty(jparsesinfo(jobj.sinfo), jobj.tkey, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRConstructorPrimaryCollectionSingletons extends MIRValueOp {
    readonly tkey: MIRNominalTypeKey;
    args: MIRArgument[];

    constructor(sinfo: SourceInfo, tkey: MIRNominalTypeKey, args: MIRArgument[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRConstructorPrimaryCollectionSingletons, sinfo, trgt);
        this.tkey = tkey;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.tkey}{${this.args.map((arg) => arg.stringify()).join(", ")}}`;
    }

    jemit(): object {
        return { ...this.jbemit(), tkey: this.tkey, args: this.args.map((arg) => arg.jemit()) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorPrimaryCollectionSingletons(jparsesinfo(jobj.sinfo), jobj.tkey, jobj.args.map((jarg: any) => MIRArgument.jparse(jarg)), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRConstructorPrimaryCollectionCopies extends MIRValueOp {
    readonly tkey: MIRNominalTypeKey;
    args: MIRArgument[];

    constructor(sinfo: SourceInfo, tkey: MIRNominalTypeKey, args: MIRArgument[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRConstructorPrimaryCollectionCopies, sinfo, trgt);
        this.tkey = tkey;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.tkey}{${this.args.map((arg) => `expand(${arg.stringify()})`).join(", ")}`;
    }

    jemit(): object {
        return { ...this.jbemit(), tkey: this.tkey, args: this.args.map((arg) => arg.jemit()) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorPrimaryCollectionCopies(jparsesinfo(jobj.sinfo), jobj.tkey, jobj.args.map((jarg: any) => MIRArgument.jparse(jarg)), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRConstructorPrimaryCollectionMixed extends MIRValueOp {
    readonly tkey: MIRNominalTypeKey;
    args: [boolean, MIRArgument][];

    constructor(sinfo: SourceInfo, tkey: MIRNominalTypeKey, args: [boolean, MIRArgument][], trgt: MIRTempRegister) {
        super(MIROpTag.MIRConstructorPrimaryCollectionMixed, sinfo, trgt);
        this.tkey = tkey;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper(this.args.map((tv) => tv[1])); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.tkey}{${this.args.map((arg) => arg[0] ? `expand(${arg[1].stringify()})` : arg[1].stringify()).join(", ")}`;
    }

    jemit(): object {
        return { ...this.jbemit(), tkey: this.tkey, args: this.args.map((arg) => [arg[0], arg[1].jemit()]) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorPrimaryCollectionMixed(jparsesinfo(jobj.sinfo), jobj.tkey, jobj.args.map((jarg: any) => [jarg[0], MIRArgument.jparse(jarg[1])]), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRConstructorTuple extends MIRValueOp {
    resultTupleType: MIRResolvedTypeKey;
    args: MIRArgument[];

    constructor(sinfo: SourceInfo, resultTupleType: MIRResolvedTypeKey, args: MIRArgument[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRConstructorTuple, sinfo, trgt);
        this.resultTupleType = resultTupleType;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = [${this.args.map((arg) => arg.stringify()).join(", ")}]`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultTupleType: this.resultTupleType, args: this.args.map((arg) => arg.jemit()) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorTuple(jparsesinfo(jobj.sinfo), jobj.resultTupleType, jobj.args.map((jarg: any) => MIRArgument.jparse(jarg)), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRConstructorRecord extends MIRValueOp {
    resultRecordType: MIRResolvedTypeKey;
    args: [string, MIRArgument][];

    constructor(sinfo: SourceInfo, resultRecordType: MIRResolvedTypeKey, args: [string, MIRArgument][], trgt: MIRTempRegister) {
        super(MIROpTag.MIRConstructorRecord, sinfo, trgt);
        this.resultRecordType = resultRecordType;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper(this.args.map((tv) => tv[1])); }

    stringify(): string {
        return `${this.trgt.stringify()} = {${this.args.map((arg) => `${arg[0]}=${arg[1].stringify()}`).join(", ")}}`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultRecordType: this.resultRecordType, args: this.args.map((arg) => [arg[0], arg[1].jemit()]) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorRecord(jparsesinfo(jobj.sinfo), jobj.resultRecordType, jobj.args.map((jarg: any) => [jarg[0], MIRArgument.jparse(jarg[1])]), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRConstructorEphemeralValueList extends MIRValueOp {
    resultEphemeralListType: MIRResolvedTypeKey;
    args: MIRArgument[];

    constructor(sinfo: SourceInfo, resultEphemeralListType: MIRResolvedTypeKey, args: MIRArgument[], trgt: MIRTempRegister) {
        super(MIROpTag.MIRConstructorEphemeralValueList, sinfo, trgt);
        this.resultEphemeralListType = resultEphemeralListType;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = [${this.args.map((arg) => arg.stringify()).join(", ")}]`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultEphemeralListType: this.resultEphemeralListType, args: this.args.map((arg) => arg.jemit()) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRConstructorEphemeralValueList(jparsesinfo(jobj.sinfo), jobj.resultEphemeralListType, jobj.args.map((jarg: any) => MIRArgument.jparse(jarg)), MIRTempRegister.jparse(jobj.trgt));
    }
}




class MIRInvokeFixedFunction extends MIRValueOp {
    resultType: MIRResolvedTypeKey;
    readonly mkey: MIRInvokeKey;
    args: MIRArgument[]; //this is args[0] for methods

    constructor(sinfo: SourceInfo, resultType: MIRResolvedTypeKey, mkey: MIRInvokeKey, args: MIRArgument[], optstatusmask: string | undefined, trgt: MIRTempRegister) {
        super(MIROpTag.MIRInvokeFixedFunction, sinfo, trgt);
        this.resultType = resultType;
        this.mkey = mkey;
        this.args = args;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.mkey}::(${this.args.map((arg) => arg.stringify()).join(", ")})`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultType: this.resultType, mkey: this.mkey, args: this.args.map((arg) => arg.jemit()) };
    }

    static jparse(jobj: any): MIROp {
        return new MIRInvokeFixedFunction(jparsesinfo(jobj.sinfo), jobj.resultType, jobj.mkey, jobj.args.map((arg: any) => MIRArgument.jparse(arg)), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRInvokeVirtualFunction extends MIRValueOp {
    resultType: MIRResolvedTypeKey;
    readonly vresolve: MIRVirtualMethodKey;
    args: MIRArgument[]; //this is args[0]
    thisInferType: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, resultType: MIRResolvedTypeKey, vresolve: MIRVirtualMethodKey, args: MIRArgument[], thisInferType: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRInvokeVirtualTarget, sinfo, trgt);
        this.resultType = resultType;
        this.vresolve = vresolve;
        this.args = args;
        this.thisInferType = thisInferType;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([...this.args]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.args[0].stringify()}.${this.vresolve}(${[...this.args].slice(1).map((arg) => arg.stringify()).join(", ")})`;
    }

    jemit(): object {
        return { ...this.jbemit(), resultType: this.resultType, vresolve: this.vresolve, args: this.args.map((arg) => arg.jemit()), thisInferType: this.thisInferType };
    }

    static jparse(jobj: any): MIROp {
        return new MIRInvokeVirtualFunction(jparsesinfo(jobj.sinfo), jobj.resultType, jobj.vresolve, jobj.args.map((arg: any) => MIRArgument.jparse(arg)), jobj.thisInferType, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRPrefixOp extends MIRValueOp {
    readonly op: string; //+, -, !
    arg: MIRArgument;
    readonly infertype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, op: string, arg: MIRArgument, infertype: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRPrefixOp, sinfo, trgt);
        this.op = op;
        this.arg = arg;
        this.infertype = infertype;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.op}${this.arg.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), op: this.op, arg: this.arg.jemit(), infertype: this.infertype };
    }

    static jparse(jobj: any): MIROp {
        return new MIRPrefixOp(jparsesinfo(jobj.sinfo), jobj.op, MIRArgument.jparse(jobj.arg), jobj.infertype, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRBinOp extends MIRValueOp {
    readonly lhsInferType: MIRResolvedTypeKey;
    lhs: MIRArgument;
    readonly op: string; //+, -, *, /
    readonly rhsInferType: MIRResolvedTypeKey;
    rhs: MIRArgument;

    constructor(sinfo: SourceInfo, lhsInferType: MIRResolvedTypeKey, lhs: MIRArgument, op: string, rhsInferType: MIRResolvedTypeKey, rhs: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRBinOp, sinfo, trgt);
        this.lhsInferType = lhsInferType;
        this.lhs = lhs;
        this.op = op;
        this.rhsInferType = rhsInferType;
        this.rhs = rhs;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.lhs, this.rhs]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.lhs.stringify()}${this.op}${this.rhs.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), lhsInferType: this.lhsInferType, lhs: this.lhs.jemit(), op: this.op, rhsInferType: this.rhsInferType, rhs: this.rhs.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRBinOp(jparsesinfo(jobj.sinfo), jobj.lhsInferType, MIRArgument.jparse(jobj.lhs), jobj.op, jobj.rhsInferType, MIRArgument.jparse(jobj.rhs), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRBinEq extends MIRValueOp {
    readonly lhsInferType: MIRResolvedTypeKey;
    lhs: MIRArgument;
    readonly op: string; //==, !=
    readonly rhsInferType: MIRResolvedTypeKey;
    rhs: MIRArgument;
    readonly relaxed: boolean;

    constructor(sinfo: SourceInfo, lhsInferType: MIRResolvedTypeKey, lhs: MIRArgument, op: string, rhsInferType: MIRResolvedTypeKey, rhs: MIRArgument, trgt: MIRTempRegister, relaxed: boolean) {
        super(MIROpTag.MIRBinEq, sinfo, trgt);
        this.lhsInferType = lhsInferType;
        this.lhs = lhs;
        this.op = op;
        this.rhsInferType = rhsInferType;
        this.rhs = rhs;
        this.relaxed = relaxed;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.lhs, this.rhs]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.lhs.stringify()}${this.op}${this.rhs.stringify()}${this.relaxed ? " | relaxed" : ""}`;
    }

    jemit(): object {
        return { ...this.jbemit(), lhsInferType: this.lhsInferType, lhs: this.lhs.jemit(), op: this.op, rhsInferType: this.rhsInferType, rhs: this.rhs.jemit(), relaxed: this.relaxed };
    }

    static jparse(jobj: any): MIROp {
        return new MIRBinEq(jparsesinfo(jobj.sinfo), jobj.lhsInferType, MIRArgument.jparse(jobj.lhs), jobj.op, jobj.rhsInferType, MIRArgument.jparse(jobj.rhs), MIRTempRegister.jparse(jobj.trgt), jobj.relaxed);
    }
}

class MIRBinLess extends MIRValueOp {
    readonly lhsInferType: MIRResolvedTypeKey;
    lhs: MIRArgument;
    readonly rhsInferType: MIRResolvedTypeKey;
    rhs: MIRArgument;
    readonly relaxed: boolean;

    constructor(sinfo: SourceInfo, lhsInferType: MIRResolvedTypeKey, lhs: MIRArgument, rhsInferType: MIRResolvedTypeKey, rhs: MIRArgument, trgt: MIRTempRegister, relaxed: boolean) {
        super(MIROpTag.MIRBinLess, sinfo, trgt);
        this.lhsInferType = lhsInferType;
        this.lhs = lhs;
        this.rhsInferType = rhsInferType;
        this.rhs = rhs;
        this.relaxed = relaxed;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.lhs, this.rhs]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.lhs.stringify()} < ${this.rhs.stringify()}${this.relaxed ? " | relaxed" : ""}`;
    }

    jemit(): object {
        return { ...this.jbemit(), lhsInferType: this.lhsInferType, lhs: this.lhs.jemit(), rhsInferType: this.rhsInferType, rhs: this.rhs.jemit(), relaxed: this.relaxed };
    }

    static jparse(jobj: any): MIROp {
        return new MIRBinLess(jparsesinfo(jobj.sinfo), jobj.lhsInferType, MIRArgument.jparse(jobj.lhs), jobj.rhsInferType, MIRArgument.jparse(jobj.rhs), MIRTempRegister.jparse(jobj.trgt), jobj.relaxed);
    }
}

class MIRBinCmp extends MIRValueOp {
    readonly lhsInferType: MIRResolvedTypeKey;
    lhs: MIRArgument;
    readonly op: string; //<, >, <=, >=
    rhs: MIRArgument;
    readonly rhsInferType: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, lhsInferType: MIRResolvedTypeKey, lhs: MIRArgument, op: string, rhsInferType: MIRResolvedTypeKey, rhs: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRBinCmp, sinfo, trgt);
        this.lhsInferType = lhsInferType;
        this.lhs = lhs;
        this.op = op;
        this.rhsInferType = rhsInferType;
        this.rhs = rhs;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.lhs, this.rhs]); }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.lhs.stringify()}${this.op}${this.rhs.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), lhsInferType: this.lhsInferType, lhs: this.lhs.jemit(), op: this.op, rhsInferType: this.rhsInferType, rhs: this.rhs.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRBinCmp(jparsesinfo(jobj.sinfo), jobj.lhsInferType, MIRArgument.jparse(jobj.lhs), jobj.op, jobj.rhsInferType, MIRArgument.jparse(jobj.rhs), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRIsTypeOfNone extends MIRValueOp {
    arg: MIRArgument;

    constructor(sinfo: SourceInfo, arg: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRIsTypeOfNone, sinfo, trgt);
        this.arg = arg;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = $isNoneType(${this.arg.stringify()})`;
    }

    jemit(): object {
        return { ...this.jbemit(), arg: this.arg.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRIsTypeOfNone(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRIsTypeOfSome extends MIRValueOp {
    arg: MIRArgument;

    constructor(sinfo: SourceInfo, arg: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRIsTypeOfSome, sinfo, trgt);
        this.arg = arg;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = $isSomeType(${this.arg.stringify()})`;
    }

    jemit(): object {
        return { ...this.jbemit(), arg: this.arg.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRIsTypeOfSome(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRIsTypeOf extends MIRValueOp {
    readonly argInferType: MIRResolvedTypeKey;
    arg: MIRArgument;
    readonly oftype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, argInferType: MIRResolvedTypeKey, arg: MIRArgument, oftype: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRIsTypeOf, sinfo, trgt);
        this.argInferType = argInferType;
        this.arg = arg;
        this.oftype = oftype;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }

    stringify(): string {
        return `${this.trgt.stringify()} = $isTypeOf(${this.arg.stringify()}, ${this.oftype})`;
    }

    jemit(): object {
        return { ...this.jbemit(), argInferType: this.argInferType, arg: this.arg.jemit(), oftype: this.oftype };
    }

    static jparse(jobj: any): MIROp {
        return new MIRIsTypeOf(jparsesinfo(jobj.sinfo), jobj.argInferType, MIRArgument.jparse(jobj.arg), jobj.oftype, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRTempRegisterAssign extends MIRFlowOp {
    src: MIRArgument;
    trgt: MIRTempRegister;

    constructor(sinfo: SourceInfo, src: MIRArgument, trgt: MIRTempRegister) {
        super(MIROpTag.MIRTempRegisterAssign, sinfo);
        this.src = src;
        this.trgt = trgt;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.src]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.src.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), src: this.src.jemit(), trgt: this.trgt.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRTempRegisterAssign(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src), MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRParameterVarStore extends MIRFlowOp {
    src: MIRArgument;
    name: MIRParameterVariable;
    readonly oftype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, src: MIRArgument, name: MIRParameterVariable, oftype: MIRResolvedTypeKey) {
        super(MIROpTag.MIRParameterVarStore, sinfo);
        this.src = src;
        this.name = name;
        this.oftype = oftype;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.src]); }
    getModVars(): MIRRegisterArgument[] { return [this.name]; }

    stringify(): string {
        return `${this.name.stringify()} = ${this.src.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), src: this.src.jemit(), name: this.name.jemit(), oftype: this.oftype };
    }

    static jparse(jobj: any): MIROp {
        return new MIRParameterVarStore(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src), MIRLocalVariable.jparse(jobj.name), jobj.oftype);
    }
}

class MIRLocalVarStore extends MIRFlowOp {
    src: MIRArgument;
    name: MIRLocalVariable;
    readonly oftype: MIRResolvedTypeKey

    constructor(sinfo: SourceInfo, src: MIRArgument, name: MIRLocalVariable, oftype: MIRResolvedTypeKey) {
        super(MIROpTag.MIRLocalVarStore, sinfo);
        this.src = src;
        this.name = name;
        this.oftype = oftype;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.src]); }
    getModVars(): MIRRegisterArgument[] { return [this.name]; }

    stringify(): string {
        return `${this.name.stringify()} = ${this.src.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), src: this.src.jemit(), name: this.name.jemit(), oftype: this.oftype };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLocalVarStore(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src), MIRLocalVariable.jparse(jobj.name), jobj.oftype);
    }
}

class MIRParameterVarStoreWithGuard extends MIRFlowOp {
    src: MIRArgument;
    name: MIRParameterVariable;
    readonly oftype: MIRResolvedTypeKey;
    readonly mask: string;
    readonly index: number;

    constructor(sinfo: SourceInfo, src: MIRArgument, name: MIRParameterVariable, oftype: MIRResolvedTypeKey, mask: string, index: number) {
        super(MIROpTag.MIRParameterVarStoreWithGuard, sinfo);
        this.src = src;
        this.name = name;
        this.oftype = oftype;
        this.mask = mask;
        this.index = index;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.src]); }
    getModVars(): MIRRegisterArgument[] { return [this.name]; }

    stringify(): string {
        return `${this.name.stringify()} = ${this.src.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), src: this.src.jemit(), name: this.name.jemit(), oftype: this.oftype, mask: this.mask, index: this.index };
    }

    static jparse(jobj: any): MIROp {
        return new MIRParameterVarStoreWithGuard(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src), MIRParameterVariable.jparse(jobj.name), jobj.oftype, jobj.mask, jobj.index);
    }
}

class MIRLocalVarStoreWithGuard extends MIRFlowOp {
    src: MIRArgument;
    name: MIRLocalVariable;
    readonly oftype: MIRResolvedTypeKey;
    readonly mask: string;
    readonly index: number;

    constructor(sinfo: SourceInfo, src: MIRArgument, name: MIRLocalVariable, oftype: MIRResolvedTypeKey, mask: string, index: number) {
        super(MIROpTag.MIRLocalVarStoreWithGuard, sinfo);
        this.src = src;
        this.name = name;
        this.oftype = oftype;
        this.mask = mask;
        this.index = index;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.src]); }
    getModVars(): MIRRegisterArgument[] { return [this.name]; }

    stringify(): string {
        return `${this.name.stringify()} = ${this.src.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), src: this.src.jemit(), name: this.name.jemit(), oftype: this.oftype, mask: this.mask, index: this.index };
    }

    static jparse(jobj: any): MIROp {
        return new MIRLocalVarStoreWithGuard(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src), MIRLocalVariable.jparse(jobj.name), , jobj.oftype, jobj.mask, jobj.index);
    }
}


class MIRPackSlice extends MIRFlowOp {
    src: MIRArgument;
    readonly sltype: MIRResolvedTypeKey;
    trgt: MIRTempRegister;

    constructor(sinfo: SourceInfo, src: MIRArgument, sltype: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRPackSlice, sinfo);
        this.src = src;
        this.sltype = sltype;
        this.trgt = trgt;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.src]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.src.stringify()}[${this.sltype}]`;
    }

    jemit(): object {
        return { ...this.jbemit(), src: this.src.jemit(), sltype: this.sltype, trgt: this.trgt.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRPackSlice(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src), jobj.sltype, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRPackExtend extends MIRFlowOp {
    basepack: MIRArgument;
    ext: MIRArgument[];
    readonly sltype: MIRResolvedTypeKey;
    trgt: MIRTempRegister;

    constructor(sinfo: SourceInfo, basepack: MIRArgument, ext: MIRArgument[], sltype: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        super(MIROpTag.MIRPackExtend, sinfo);
        this.basepack = basepack;
        this.ext = ext;
        this.sltype = sltype;
        this.trgt = trgt;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.basepack, ...this.ext]); }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        return `${this.trgt.stringify()} = ${this.sltype}@(|${this.basepack.stringify()}, ${this.ext.map((e) => e.stringify()).join(", ")}|)`;
    }

    jemit(): object {
        return { ...this.jbemit(), basepack: this.basepack.jemit(), ext: this.ext.map((e) => e.jemit()), sltype: this.sltype, trgt: this.trgt.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRPackExtend(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.basepack), jobj.ext.map((e: string) => MIRArgument.jparse(e)), jobj.sltype, MIRTempRegister.jparse(jobj.trgt));
    }
}

class MIRReturnAssign extends MIRFlowOp {
    src: MIRArgument;
    name: MIRVariable;

    constructor(sinfo: SourceInfo, src: MIRArgument, name?: MIRVariable) {
        super(MIROpTag.MIRReturnAssign, sinfo);
        this.src = src;
        this.name = name || new MIRVariable("$__ir_ret__");
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.src]); }
    getModVars(): MIRRegisterArgument[] { return [this.name]; }

    stringify(): string {
        return `${this.name.stringify()} = ${this.src.stringify()}`;
    }

    jemit(): object {
        return { ...this.jbemit(), src: this.src.jemit(), name: this.name.jemit() };
    }

    static jparse(jobj: any): MIROp {
        return new MIRReturnAssign(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.src), MIRVariable.jparse(jobj.name));
    }
}

class MIRAbort extends MIRFlowOp {
    readonly info: string;

    constructor(sinfo: SourceInfo, info: string) {
        super(MIROpTag.MIRAbort, sinfo);
        this.info = info;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `abort -- ${this.info}`;
    }

    jemit(): object {
        return { ...this.jbemit(), info: this.info };
    }

    static jparse(jobj: any): MIROp {
        return new MIRAbort(jparsesinfo(jobj.sinfo), jobj.info);
    }
}

class MIRDebug extends MIRFlowOp {
    value: MIRArgument | undefined;

    constructor(sinfo: SourceInfo, value: MIRArgument | undefined) {
        super(MIROpTag.MIRDebug, sinfo);
        this.value = value;
    }

    getUsedVars(): MIRRegisterArgument[] { return this.value !== undefined ? varsOnlyHelper([this.value]) : []; }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        if (this.value === undefined) {
            return "_debug break";
        }
        else {
            return `_debug ${this.value.stringify()}`;
        }
    }

    jemit(): object {
        return { ...this.jbemit(), value: this.value ? [this.value.jemit()] : null };
    }

    static jparse(jobj: any): MIROp {
        return new MIRDebug(jparsesinfo(jobj.sinfo), jobj.value ? MIRArgument.jparse(jobj.value[0]) : undefined);
    }
}

class MIRJump extends MIRJumpOp {
    readonly trgtblock: string;

    constructor(sinfo: SourceInfo, blck: string) {
        super(MIROpTag.MIRJump, sinfo);
        this.trgtblock = blck;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `jump ${this.trgtblock}`;
    }

    jemit(): object {
        return { ...this.jbemit(), trgtblock: this.trgtblock };
    }

    static jparse(jobj: any): MIROp {
        return new MIRJump(jparsesinfo(jobj.sinfo), jobj.trgtblock);
    }
}

class MIRVarLifetimeStart extends MIRJumpOp {
    readonly name: string;
    readonly rtype: MIRResolvedTypeKey;

    constructor(sinfo: SourceInfo, name: string, rtype: MIRResolvedTypeKey) {
        super(MIROpTag.MIRVarLifetimeStart, sinfo);
        this.name = name;
        this.rtype = rtype;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `v-begin ${this.name}`;
    }

    jemit(): object {
        return { ...this.jbemit(), name: this.name, rtype: this.rtype };
    }

    static jparse(jobj: any): MIROp {
        return new MIRVarLifetimeStart(jparsesinfo(jobj.sinfo), jobj.name, jobj.rtype);
    }
}

class MIRVarLifetimeEnd extends MIRJumpOp {
    readonly name: string;

    constructor(sinfo: SourceInfo, name: string) {
        super(MIROpTag.MIRVarLifetimeEnd, sinfo);
        this.name = name;
    }

    getUsedVars(): MIRRegisterArgument[] { return []; }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `v-end ${this.name}`;
    }

    jemit(): object {
        return { ...this.jbemit(), name: this.name };
    }

    static jparse(jobj: any): MIROp {
        return new MIRVarLifetimeEnd(jparsesinfo(jobj.sinfo), jobj.name);
    }
}

class MIRJumpCond extends MIRJumpOp {
    arg: MIRArgument;
    readonly trueblock: string;
    readonly falseblock: string;

    constructor(sinfo: SourceInfo, arg: MIRArgument, trueblck: string, falseblck: string) {
        super(MIROpTag.MIRJumpCond, sinfo);
        this.arg = arg;
        this.trueblock = trueblck;
        this.falseblock = falseblck;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `cjump ${this.arg.stringify()} ${this.trueblock} ${this.falseblock}`;
    }

    jemit(): object {
        return { ...this.jbemit(), arg: this.arg.jemit(), trueblock: this.trueblock, falseblock: this.falseblock };
    }

    static jparse(jobj: any): MIROp {
        return new MIRJumpCond(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.trueblock, jobj.falseblock);
    }
}

class MIRJumpNone extends MIRJumpOp {
    arg: MIRArgument;
    readonly noneblock: string;
    readonly someblock: string;

    constructor(sinfo: SourceInfo, arg: MIRArgument, noneblck: string, someblck: string) {
        super(MIROpTag.MIRJumpNone, sinfo);
        this.arg = arg;
        this.noneblock = noneblck;
        this.someblock = someblck;
    }

    getUsedVars(): MIRRegisterArgument[] { return varsOnlyHelper([this.arg]); }
    getModVars(): MIRRegisterArgument[] { return []; }

    stringify(): string {
        return `njump ${this.arg.stringify()} ${this.noneblock} ${this.someblock}`;
    }

    jemit(): object {
        return { ...this.jbemit(), arg: this.arg.jemit(), noneblock: this.noneblock, someblock: this.someblock };
    }

    static jparse(jobj: any): MIROp {
        return new MIRJumpNone(jparsesinfo(jobj.sinfo), MIRArgument.jparse(jobj.arg), jobj.noneblock, jobj.someblock);
    }
}

class MIRPhi extends MIRFlowOp {
    src: Map<string, MIRRegisterArgument>;
    trgt: MIRRegisterArgument;

    constructor(sinfo: SourceInfo, src: Map<string, MIRRegisterArgument>, trgt: MIRRegisterArgument) {
        super(MIROpTag.MIRPhi, sinfo);
        this.src = src;
        this.trgt = trgt;
    }

    getUsedVars(): MIRRegisterArgument[] {
        let phis: MIRRegisterArgument[] = [];
        this.src.forEach((v) => phis.push(v));

        return phis;
    }
    getModVars(): MIRRegisterArgument[] { return [this.trgt]; }

    stringify(): string {
        let phis: string[] = [];
        this.src.forEach((v, k) => phis.push(`${v.stringify()} -- ${k}`));
        phis.sort();

        return `${this.trgt.stringify()} = (${phis.join(", ")})`;
    }

    jemit(): object {
        const phis = [...this.src].map((phi) => [phi[0], phi[1].jemit()]);
        return { ...this.jbemit(), src: phis, trgt: this.trgt.jemit() };
    }

    static jparse(jobj: any): MIROp {
        let phis = new Map<string, MIRRegisterArgument>();
        jobj.src.forEach((phi: [string, any]) => phis.set(phi[0], MIRRegisterArgument.jparse(phi[1])));
        return new MIRPhi(jparsesinfo(jobj.sinfo), phis, MIRRegisterArgument.jparse(jobj.trgt));
    }
}

class MIRBasicBlock {
    readonly label: string;
    ops: MIROp[];

    constructor(label: string, ops: MIROp[]) {
        this.label = label;
        this.ops = ops;
    }

    jsonify(): { label: string, line: number, ops: string[] } {
        const jblck = {
            label: this.label,
            line: (this.ops.length !== 0) ? this.ops[0].sinfo.line : -1,
            ops: this.ops.map((op) => op.stringify())
        };

        return jblck;
    }

    jemit(): object {
        return { label: this.label, ops: this.ops.map((op) => op.jemit()) };
    }

    static jparse(jobj: any): MIRBasicBlock {
        return new MIRBasicBlock(jobj.label, jobj.ops.map((op: any) => MIROp.jparse(op)));
    }
}

class MIRBody {
    readonly file: string;
    readonly sinfo: SourceInfo;

    body: Map<string, MIRBasicBlock>;
    vtypes: Map<string, MIRResolvedTypeKey> | undefined;

    constructor(file: string, sinfo: SourceInfo, body: Map<string, MIRBasicBlock>, vtypes?: Map<string, MIRResolvedTypeKey>) {
        this.file = file;
        this.sinfo = sinfo;

        this.body = body;
        this.vtypes = vtypes;
    }

    jsonify(): any {
        let blocks: any[] = [];
        topologicalOrder(this.body).forEach((v, k) => blocks.push(v.jsonify()));

        return blocks;
    }

    dgmlify(siginfo: string): string {
        const blocks = topologicalOrder(this.body);
        const flow = computeBlockLinks(this.body);

        const xmlescape = (str: string) => {
            return str.replace(/&/g, "&amp;")
                .replace(/</g, "&lt;")
                .replace(/>/g, "&gt;")
                .replace(/"/g, "&quot;")
                .replace(/'/g, "&apos;");
        };

        let nodes: string[] = [`<Node Id="fdecl" Label="${siginfo}"/>`];
        let links: string[] = [`<Link Source="fdecl" Target="entry"/>`];
        blocks.forEach((b) => {
            const ndata = b.jsonify();
            const dstring = `L: ${ndata.label} &#10;  ` + ndata.ops.map((op) => xmlescape(op)).join("&#10;  ");
            nodes.push(`<Node Id="${ndata.label}" Label="${dstring}"/>`);

            (flow.get(ndata.label) as FlowLink).succs.forEach((succ) => {
                links.push(`<Link Source="${ndata.label}" Target="${succ}"/>`);
            });
        });

        return `<?xml version="1.0" encoding="utf-8"?>
        <DirectedGraph Title="DrivingTest" xmlns="http://schemas.microsoft.com/vs/2009/dgml">
           <Nodes>
                ${nodes.join("\n")}
           </Nodes>
           <Links>
                ${links.join("\n")}
           </Links>
        </DirectedGraph>`;
    }

    jemit(): object {
        const blocks = topologicalOrder(this.body).map((blck) => blck.jemit());
        const vtypes = this.vtypes !== undefined ? ([...this.vtypes].sort((a, b) => a[0].localeCompare(b[0]))) : undefined;
        return { file: this.file, sinfo: jemitsinfo(this.sinfo), blocks: blocks, vtypes: vtypes };
    }

    static jparse(jobj: any): MIRBody {
        let body = new Map<string, MIRBasicBlock>();
        jobj.blocks.map((blck: any) => MIRBasicBlock.jparse(blck)).forEach((blck: MIRBasicBlock) => body.set(blck.label, blck));

        if (jobj.vtypes === undefined) {
            return new MIRBody(jobj.file, jparsesinfo(jobj.sinfo), body);
        }
        else {
            let vtypes = new Map<string, MIRResolvedTypeKey>();
            jobj.vtypes.forEach((vtype: [string, string]) => vtypes.set(vtype[0], vtype[1]));

            return new MIRBody(jobj.file, jparsesinfo(jobj.sinfo), body, vtypes);
        }
    }
}

export {
    MIRGlobalKey, MIRFieldKey, MIRInvokeKey, MIRResolvedTypeKey, MIRVirtualMethodKey,
    MIRArgument, MIRRegisterArgument, MIRTempRegister, MIRGlobalVariable, MIRVariableArgument, MIRParameterVariable, MIRLocalVariable, 
    MIRConstantArgument, MIRConstantNone, MIRConstantTrue, MIRConstantFalse, MIRConstantInt, MIRConstantNat, MIRConstantBigInt, MIRConstantBigNat, MIRConstantRational, MIRConstantComplex, MIRConstantFloat, MIRConstantDecmial, MIRConstantString, MIRConstantRegex, MIRConstantStringOf,
    MIROpTag, MIROp, MIRNop, MIRDeadFlow, MIRValueOp, MIRFlowOp, MIRJumpOp,
    MIRLoadConst, MIRLoadConstDataString,
    MIRTupleHasIndex, MIRRecordHasProperty,
    MIRLoadTupleIndex, MIRCheckedLoadTupleIndex, MIRLoadTupleIndexTry, MIRLoadRecordProperty, MIRCheckedLoadRecordProperty, MIRLoadRecordPropertyTry,
    MIRTempRegisterAssign, MIRParameterVarStore, MIRLocalVarStore, MIRParameterVarStoreWithGuard, MIRLocalVarStoreWithGuard,
    MIRLoadField,
    MIRLoadFromEpehmeralList, MIRMultiLoadFromEpehmeralList,

    MIRBody
};
