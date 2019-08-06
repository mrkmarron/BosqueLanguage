//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIROp, MIROpTag, MIRLoadConst, MIRConstantArgument, MIRArgument, MIRRegisterArgument, MIRAccessArgVariable, MIRAccessLocalVariable, MIRConstructorTuple, MIRAccessFromIndex } from "../../compiler/mir_ops";
import { MIRType, MIRAssembly, MIRTupleType } from "../../compiler/mir_assembly";

function NOT_IMPLEMENTED(action: string): never {
    throw new Error(`Not Implemented: ${action}`);
}

const smt_header = `
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
`;

const exact_values_template = `
(declare-datatypes ( (BNone 0) (BBool 0) (BInt 0) (BString 0)
                     (BTuple0 0) (BTuple1 1) (BTuple2 2) (BTuple3 3)
                     (BRecord0 0) (BRecord1 1) (BRecord2 2) (BRecord3 3)
                     (BEntity0 0) (BEntity1 1) (BEntity2 2) (BEntity3 3)
                     ) (
    ( (bsq_none) )
    ( (bsq_true) (bsq_false) )
    ( (bsq_int (bsq_int_value Int)) )
    ( (bsq_string (bsq_string_value String)) )

    ( (bsq_tuple0) )
    ( par (T0) ((bsq_tuple1 (bsq_tuple1_value0 T0))) )
    ( par (T0 T1) ((bsq_tuple2 (bsq_tuple2_value0 T0) (bsq_tuple2_value1 T1))) )
    ( par (T0 T1 T2) ((bsq_tuple3 (bsq_tuple3_value0 T0) (bsq_tuple3_value1 T1) (bsq_tuple3_value2 T2))) )

    ( (bsq_record0) )
    ( par (T0) ((bsq_record1 (bsq_record1_name0 String) (bsq_record1_value0 T0))) )
    ( par (T0 T1) ((bsq_record2 (bsq_record2_name0 String) (bsq_record2_value0 T0) (bsq_record2_name1 String) (bsq_record2_value1 T1))) )
    ( par (T0 T1 T2) ((bsq_record3 (bsq_record3_name0 String) (bsq_record3_value0 T0) (bsq_record3_name1 String) (bsq_record3_value1 T1) (bsq_record3_name2 String) (bsq_record3_value2 T2))) )

    ( (bsq_entity0 (bsq_entity0_type String)) )
    ( par (T0) ((bsq_entity1 (bsq_entity1_type String) (bsq_entity1_field0 String) (bsq_entity1_value0 T0))) )
    ( par (T0 T1) ((bsq_entity2 (bsq_entity1_type String) (bsq_entity2_field0 String) (bsq_entity2_value0 T0) (bsq_entity2_field1 String) (bsq_value2_value1 T1))) )
    ( par (T0 T1 T2) ((bsq_entity3 (bsq_entity1_type String) (bsq_entity3_field0 String) (bsq_entity3_value0 T0) (bsq_entity3_field1 String) (bsq_entity3_value1 T1) (bsq_entity3_field2 String) (bsq_entity3_value2 T2))) )
))
`;

const general_values = `
(declare-datatypes ( (BTuple 0)
                     (BRecord 0)
                     (BEntity 0)
                     (BTerm 0)
                     ) (
    ( (bsq_tuple (bsq_tuple_size Int) (bsq_tuple_value0 BTerm) (bsq_tuple_value1 BTerm) (bsq_tuple_value2 BTerm)) )
    ( (bsq_record (bsq_record_size Int) (bsq_record_name0 String) (bsq_record_value0 BTerm) (bsq_record_name1 String) (bsq_record_value1 BTerm) (bsq_record_name2 String) (bsq_record_value2 BTerm)) )
    ( (bsq_entity (bsq_entity_type String) (bsq_record_size Int) (bsq_entity_name0 String) (bsq_entity_value0 BTerm) (bsq_entity_name1 String) (bsq_entity_value1 BTerm) (bsq_entity_name2 String) (bsq_entity_value2 BTerm)) )

    ( (bsq_term_none) (bsq_term_bool (bsq_term_bool_value BBool)) (bsq_term_int (bsq_term_int_value BInt)) (bsq_term_string (bsq_term_string_value BString)) (bsq_term_tuple (bsq_term_tuple_value BTuple)) )
))

(declare-datatypes ( (Result 1)
                     ) (
    (par (T) ((result_error (error_msg String)) (result_success (result_value T0)) ))
))
`;

class SMTLIBGenerator {
    readonly assembly: MIRAssembly;

    constructor(assembly: MIRAssembly) {
        this.assembly = assembly;
    }

    isTypeExact(type: MIRType): boolean {
        xxxx;
    }

    typeToSMT2(type: MIRType): string {
        xxxx;
    }

    constToSMT2(cv: MIRConstantArgument): string {
        xxxx;
    }

    varToSMT2(vv: MIRRegisterArgument): string {
        xxxx;
    }

    argToSMT2(arg: MIRArgument): string {
        xxxx;
    }

    generateMIRConstructorTuple(op: MIRConstructorTuple, vtypes: Map<string, MIRType>): string {
        const ttype = (this.assembly.typeMap.get(op.tupkey) as MIRType);
        const tupinfo = ttype.options[0] as MIRTupleType;

        vtypes.set(op.trgt.nameID, ttype);
        if (this.isTypeExact(ttype)) {
            const tc = `(bsq_tuple${tupinfo.entries.length} ${op.args.map((arg) => this.argToSMT2(arg))})`;
            return `((${this.varToSMT2(op.trgt)} ${tc}))`;
        }
        else {
            NOT_IMPLEMENTED("generateMIRConstructorTuple -- else branch");
        }
    }

    generateMIRAccessFromIndex(op: MIRAccessFromIndex, vtypes: Map<string, MIRType>): string {
        const ttype = (vtypes.get(op.arg.nameID) as MIRType);
        const tupinfo = ttype.options[0] as MIRTupleType;

        vtypes.set(op.trgt.nameID, xxxx;);
        if (this.isTypeExact(ttype)) {
            const tc = `(bsq_tuple${tupinfo.entries.length} ${op.args.map((arg) => this.argToSMT2(arg))})`;
            return `((${this.varToSMT2(op.trgt)} ${tc}))`;
        }
        else {
            NOT_IMPLEMENTED("generateMIRConstructorTuple -- else branch");
        }
    }

    generateSMTScope(op: MIROp, scope: string[], vtypes: Map<string, MIRType>): [MIROpTag, string] | undefined {
        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const lcv = (op as MIRLoadConst);
                scope.push(`((${this.varToSMT2(lcv.trgt)} ${this.constToSMT2(lcv.src)}))`);
                vtypes.set(lcv.trgt.nameID, xxxx);
                return undefined;
            }
            case MIROpTag.MIRLoadConstTypedString:  {
                NOT_IMPLEMENTED("MIRLoadConstTypedString");
                break;
            }
            case MIROpTag.MIRAccessConstantValue: {
                NOT_IMPLEMENTED("MIRAccessConstantValue");
                break;
            }
            case MIROpTag.MIRLoadFieldDefaultValue: {
                NOT_IMPLEMENTED("MIRLoadFieldDefaultValue");
                break;
            }
            case MIROpTag.MIRAccessArgVariable: {
                const lav = (op as MIRAccessArgVariable);
                scope.push(`((${this.varToSMT2(lav.trgt)} ${this.varToSMT2(lav.name)}))`);
                vtypes.set(lav.trgt.nameID, vtypes.get(lav.name.nameID) as MIRType);
                return undefined;
            }
            case MIROpTag.MIRAccessLocalVariable: {
                const llv = (op as MIRAccessLocalVariable);
                scope.push(`((${this.varToSMT2(llv.trgt)} ${this.varToSMT2(llv.name)}))`);
                vtypes.set(llv.trgt.nameID, vtypes.get(llv.name.nameID) as MIRType);
                return undefined;
            }
            case MIROpTag.MIRConstructorPrimary: {
                NOT_IMPLEMENTED("MIRConstructorPrimary");
                break;
            }
            case MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
                NOT_IMPLEMENTED("MIRConstructorPrimaryCollectionEmpty");
                break;
            }
            case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                NOT_IMPLEMENTED("MIRConstructorPrimaryCollectionSingletons");
                break;
            }
            case MIROpTag.MIRConstructorPrimaryCollectionCopies: {
                NOT_IMPLEMENTED("MIRConstructorPrimaryCollectionCopies");
                break;
            }
            case MIROpTag.MIRConstructorPrimaryCollectionMixed: {
                NOT_IMPLEMENTED("MIRConstructorPrimaryCollectionMixed");
                break;
            }
            case MIROpTag.MIRConstructorTuple: {
                const tc = op as MIRConstructorTuple;
                scope.push(this.generateMIRConstructorTuple(tc), vtypes);
                return undefined;
            }
            case MIROpTag.MIRConstructorRecord: {
                NOT_IMPLEMENTED("MIRConstructorRecord");
                break;
            }
            case MIROpTag.MIRAccessFromIndex: {
                const ai = op as MIRAccessFromIndex;
                ai.arg = processSSA_Use(ai.arg, remap);
                processValueOpTempSSA(ai, remap, ctrs);
                break;
            }
            case MIROpTag.MIRProjectFromIndecies: {
                NOT_IMPLEMENTED("MIRProjectFromIndecies");
                break;
            }
            case MIROpTag.MIRAccessFromProperty: {
                NOT_IMPLEMENTED("MIRAccessFromProperty");
                break;
            }
            case MIROpTag.MIRProjectFromProperties: {
                NOT_IMPLEMENTED("MIRProjectFromProperties");
                break;
            }
            case MIROpTag.MIRAccessFromField: {
                NOT_IMPLEMENTED("MIRAccessFromField");
                break;
            }
            case MIROpTag.MIRProjectFromFields: {
                NOT_IMPLEMENTED("MIRProjectFromFields");
                break;
            }
            case MIROpTag.MIRProjectFromTypeTuple: {
                NOT_IMPLEMENTED("MIRProjectFromTypeTuple");
                break;
            }
            case MIROpTag.MIRProjectFromTypeRecord: {
                NOT_IMPLEMENTED("MIRProjectFromTypeRecord");
                break;
            }
            case MIROpTag.MIRProjectFromTypeConcept: {
                NOT_IMPLEMENTED("MIRProjectFromTypeConcept");
                break;
            }
            case MIROpTag.MIRModifyWithIndecies: {
                const mi = op as MIRModifyWithIndecies;
                mi.arg = processSSA_Use(mi.arg, remap);
                mi.updates = processSSAUse_RemapStructuredArgs<[number, MIRArgument]>(mi.updates, (u) => [u[0], processSSA_Use(u[1], remap)]);
                processValueOpTempSSA(mi, remap, ctrs);
                break;
            }
            case MIROpTag.MIRModifyWithProperties: {
                NOT_IMPLEMENTED("MIRModifyWithProperties");
                break;
            }
            case MIROpTag.MIRModifyWithFields: {
                NOT_IMPLEMENTED("MIRModifyWithFields");
                break;
            }
            case MIROpTag.MIRStructuredExtendTuple: {
                NOT_IMPLEMENTED("MIRStructuredExtendTuple");
                break;
            }
            case MIROpTag.MIRStructuredExtendRecord: {
                NOT_IMPLEMENTED("MIRStructuredExtendRecord");
                break;
            }
            case MIROpTag.MIRStructuredExtendObject: {
                NOT_IMPLEMENTED("MIRStructuredExtendObject");
                break;
            }
            case MIROpTag.MIRInvokeFixedFunction: {
                const invk = op as MIRInvokeFixedFunction;
                invk.args = processSSAUse_RemapArgs(invk.args, remap);
                processValueOpTempSSA(invk, remap, ctrs);
                break;
            }
            case MIROpTag.MIRInvokeVirtualTarget: {
                NOT_IMPLEMENTED("MIRInvokeVirtualTarget");
                break;
            }
            case MIROpTag.MIRPrefixOp: {
                const pfx = op as MIRPrefixOp;
                pfx.arg = processSSA_Use(pfx.arg, remap);
                processValueOpTempSSA(pfx, remap, ctrs);
                break;
            }
            case MIROpTag.MIRBinOp: {
                const bop = op as MIRBinOp;
                bop.lhs = processSSA_Use(bop.lhs, remap);
                bop.rhs = processSSA_Use(bop.rhs, remap);
                processValueOpTempSSA(bop, remap, ctrs);
                break;
            }
            case MIROpTag.MIRBinEq: {
                const beq = op as MIRBinEq;
                beq.lhs = processSSA_Use(beq.lhs, remap);
                beq.rhs = processSSA_Use(beq.rhs, remap);
                processValueOpTempSSA(beq, remap, ctrs);
                break;
            }
            case MIROpTag.MIRBinCmp: {
                const bcp = op as MIRBinCmp;
                bcp.lhs = processSSA_Use(bcp.lhs, remap);
                bcp.rhs = processSSA_Use(bcp.rhs, remap);
                processValueOpTempSSA(bcp, remap, ctrs);
                break;
            }
            case MIROpTag.MIRIsTypeOfNone: {
                const ton = op as MIRIsTypeOfNone;
                ton.arg = processSSA_Use(ton.arg, remap);
                processValueOpTempSSA(ton, remap, ctrs);
                break;
            }
            case MIROpTag.MIRIsTypeOfSome: {
                const tos = op as MIRIsTypeOfSome;
                tos.arg = processSSA_Use(tos.arg, remap);
                processValueOpTempSSA(tos, remap, ctrs);
                break;
            }
            case MIROpTag.MIRIsTypeOf: {
                const tog = op as MIRIsTypeOf;
                tog.arg = processSSA_Use(tog.arg, remap);
                processValueOpTempSSA(tog, remap, ctrs);
                break;
            }
            case MIROpTag.MIRRegAssign: {
                const regop = op as MIRRegAssign;
                regop.src = processSSA_Use(regop.src, remap);
                regop.trgt = convertToSSA(regop.trgt, remap, ctrs) as MIRTempRegister;
                break;
            }
            case MIROpTag.MIRTruthyConvert: {
                const tcop = op as MIRTruthyConvert;
                tcop.src = processSSA_Use(tcop.src, remap);
                tcop.trgt = convertToSSA(tcop.trgt, remap, ctrs) as MIRTempRegister;
                break;
            }
            case MIROpTag.MIRLogicStore: {
                const llop = op as MIRLogicStore;
                llop.lhs = processSSA_Use(llop.lhs, remap);
                llop.rhs = processSSA_Use(llop.rhs, remap);
                llop.trgt = convertToSSA(llop.trgt, remap, ctrs) as MIRTempRegister;
                break;
            }
            case MIROpTag.MIRVarStore: {
                const vs = op as MIRVarStore;
                vs.src = processSSA_Use(vs.src, remap);
                vs.name = convertToSSA(vs.name, remap, ctrs) as MIRVariable;
                break;
            }
            case MIROpTag.MIRReturnAssign: {
                const ra = op as MIRReturnAssign;
                ra.src = processSSA_Use(ra.src, remap);
                ra.name = convertToSSA(ra.name, remap, ctrs) as MIRVariable;
                break;
            }
            case MIROpTag.MIRAbort: {
                xxxx;
                break;
            }
            case MIROpTag.MIRDebug: {
                const dbg = op as MIRDebug;
                if (dbg.value !== undefined) {
                    dbg.value = processSSA_Use(dbg.value, remap);
                }
                break;
            }
            case MIROpTag.MIRJump: {
                break;
            }
            case MIROpTag.MIRJumpCond: {
                const cjop = op as MIRJumpCond;
                cjop.arg = processSSA_Use(cjop.arg, remap);
                break;
            }
            case MIROpTag.MIRJumpNone: {
                const njop = op as MIRJumpNone;
                njop.arg = processSSA_Use(njop.arg, remap);
                break;
            }
            case MIROpTag.MIRVarLifetimeStart:
            case MIROpTag.MIRVarLifetimeEnd: {
                break;
            }
            default:
                assert(false);
                break;
        }
    }
}

export {
    SMTLIBGenerator
};
