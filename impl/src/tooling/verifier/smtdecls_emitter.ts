//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { MIRAssembly, MIRConceptType, MIREntityType, MIREntityTypeDecl, MIRInvokeDecl, MIRRecordType, MIRSpecialTypeCategory, MIRTupleType, MIRType } from "../../compiler/mir_assembly";
import { constructCallGraphInfo, markSafeCalls } from "../../compiler/mir_callg";
import { MIRInvokeKey } from "../../compiler/mir_ops";
import { SMTBodyEmitter } from "./smtbody_emitter";
import { SMTTypeEmitter } from "./smttype_emitter";
import { SMTAssembly, SMTConstantDecl, SMTEphemeralListDecl, SMTFunction, SMTRecordDecl, SMTTupleDecl } from "./smt_assembly";
import { SMTExp, VerifierOptions } from "./smt_exp";

const BuiltinEntityDeclNames = [
    "None",
    "Bool",
    "Int",
    "Nat",
    "BigInt",
    "BigNat",
    "Rational",
    "Float",
    "Decimal",
    "String",
    "ISOTime", 
    "LogicalTime",
    "Regex"
];

class SMTEmitter {
    readonly temitter: SMTTypeEmitter;
    readonly bemitter: SMTBodyEmitter;
    readonly assembly: SMTAssembly;

    private lastVInvokeIdx = 0;
    private lastVOperatorIdx = 0;
    private lastVEntityUpdateIdx = 0;

    constructor(temitter: SMTTypeEmitter, bemitter: SMTBodyEmitter, assembly: SMTAssembly) {
        this.temitter = temitter;
        this.bemitter = bemitter;
        this.assembly = assembly;
    }

    private generateAPITypeConstructorFunction(trgtType: MIRType, depthexp: SMTExp, widthexp: SMTExp): SMTExp {
        xxxx;
    }

    private processISequenceTypeDecl(vdecl: MIREntityTypeDecl) {
        xxxx;
    }

    private processVectorTypeDecl(vdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
    
    private processListTypeDecl(vdecl: MIREntityTypeDecl) {
        xxxx;
    }
        
    private processStackTypeDecl(vdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
        
    private processQueueTypeDecl(vdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
       
    private processSetTypeDecl(vdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
        
    private processDynamicSetTypeDecl(vdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
        
    private processMapTypeDecl(vdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
    
    private processDynamicMapTypeDecl(vdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }

    private processEntityDecl(vdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }

    private processVirtualInvokes() {
        for(let i = this.lastVInvokeIdx; i < this.bemitter.requiredVirtualFunctionInvokes.length; ++i) {
            this.bemitter.generateVirtualFunctionInvoke(this.bemitter.requiredVirtualFunctionInvokes[i]);
        }
        this.lastVInvokeIdx = this.bemitter.requiredVirtualFunctionInvokes.length;

        for(let i = this.lastVOperatorIdx; i < this.bemitter.requiredVirtualOperatorInvokes.length; ++i) {
            this.bemitter.generateVirtualOperatorInvoke(this.bemitter.requiredVirtualOperatorInvokes[i]);
        }
        this.lastVOperatorIdx = this.bemitter.requiredVirtualOperatorInvokes.length;
    }

    private processVirtualEntityUpdates() {
        for(let i = this.lastVEntityUpdateIdx; i < this.bemitter.requiredUpdateVirtualEntity.length; ++i) {
            this.bemitter.generateUpdateEntityFieldVirtual(this.bemitter.requiredUpdateVirtualEntity[i]);
        }
        this.lastVInvokeIdx = this.bemitter.requiredUpdateVirtualEntity.length;
    }

    static generateSMTAssembly(assembly: MIRAssembly, vopts: VerifierOptions, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, maxgas: number): SMTAssembly {
        const callsafety = markSafeCalls([entrypoint], assembly, errorTrgtPos);

        const temitter = new SMTTypeEmitter(assembly, vopts);
        const bemitter = new SMTBodyEmitter(assembly, temitter, vopts, callsafety, errorTrgtPos);
        const smtassembly = new SMTAssembly(vopts);

        let smtemit = new SMTEmitter(temitter, bemitter, smtassembly);

        let doneset = new Set<MIRInvokeKey>();
        const cginfo = constructCallGraphInfo([entrypoint], assembly);
        const rcg = [...cginfo.topologicalOrder].reverse();

        for (let i = 0; i < rcg.length; ++i) {
            const cn = rcg[i];
            if(doneset.has(cn.invoke)) {
                continue;
            }

            const cscc = cginfo.recursive.find((scc) => scc.has(cn.invoke));
            const currentSCC = cscc || new Set<string>();
            let worklist = cscc !== undefined ? [...cscc].sort() : [cn.invoke];

            let gasmax: number | undefined = cscc !== undefined ? maxgas : 1;
            for (let gasctr = 1; gasctr <= gasmax; gasctr++) {
                for (let mi = 0; mi < worklist.length; ++mi) {
                    const ikey = worklist[mi];

                    let gas: number | undefined = undefined;
                    let gasdown: number | undefined = undefined;
                    if (gasctr !== gasmax) {
                        gas = gasctr;
                        gasdown = gasctr - 1;
                    }
                    else {
                        gasdown = gasmax - 1;
                    }

                    const idcl = (assembly.invokeDecls.get(ikey) || assembly.primitiveInvokeDecls.get(ikey)) as MIRInvokeDecl;
                    const finfo = smtemit.bemitter.generateSMTInvoke(idcl, currentSCC, gas, gasdown);
                    smtemit.processVirtualInvokes();
                    smtemit.processVirtualEntityUpdates();

                    if (finfo !== undefined) {
                        if (finfo instanceof SMTFunction) {
                            smtemit.assembly.functions.push(finfo);
                        }
                        else {
                            smtemit.assembly.uninterpfunctions.push(finfo);
                        }
                    }

                    const rtype = smtemit.temitter.getSMTTypeFor(smtemit.temitter.getMIRType(idcl.resultType));
                    if(smtemit.assembly.resultTypes.find((rtt) => rtt.ctype.name === rtype.name) === undefined) {
                        smtemit.assembly.resultTypes.push(({hasFlag: false, rtname: idcl.resultType, ctype: rtype}));
                    }
                }

                if(cscc !== undefined) {
                    cscc.forEach((v) => doneset.add(v));
                }
            }
        }   

        smtemit.bemitter.requiredLoadVirtualTupleIndex.forEach((rvlt) => smtemit.assembly.functions.push(smtemit.bemitter.generateLoadTupleIndexVirtual(rvlt)));
        smtemit.bemitter.requiredLoadVirtualRecordProperty.forEach((rvlr) => smtemit.assembly.functions.push(smtemit.bemitter.generateLoadRecordPropertyVirtual(rvlr)));
        smtemit.bemitter.requiredLoadVirtualEntityField.forEach((rvle) => smtemit.assembly.functions.push(smtemit.bemitter.generateLoadEntityFieldVirtual(rvle)));
        
        smtemit.bemitter.requiredProjectVirtualTupleIndex.forEach((rvpt) => smtemit.assembly.functions.push(smtemit.bemitter.generateProjectTupleIndexVirtual(rvpt)));
        smtemit.bemitter.requiredProjectVirtualRecordProperty.forEach((rvpr) => smtemit.assembly.functions.push(smtemit.bemitter.generateProjectRecordPropertyVirtual(rvpr)));
        smtemit.bemitter.requiredProjectVirtualEntityField.forEach((rvpe) => smtemit.assembly.functions.push(smtemit.bemitter.generateProjectEntityFieldVirtual(rvpe)));
    
        smtemit.bemitter.requiredUpdateVirtualTuple.forEach((rvut) => smtemit.assembly.functions.push(smtemit.bemitter.generateUpdateTupleIndexVirtual(rvut)));
        smtemit.bemitter.requiredUpdateVirtualRecord.forEach((rvur) => smtemit.assembly.functions.push(smtemit.bemitter.generateUpdateRecordPropertyVirtual(rvur)));

        assembly.entityDecls.forEach((edcl) => {
            const mirtype = smtemit.temitter.getMIRType(edcl.tkey);
            const ttag = `TypeTag_${smtemit.temitter.getSMTTypeFor(mirtype)}`;

            smtemit.assembly.typeTags.push(ttag);
            if(assembly.subtypeOf(mirtype, smtemit.temitter.getMIRType("NSCore::KeyType"))) {
                smtemit.assembly.keytypeTags.push(ttag);
            }

            if(edcl.specialDecls.has(MIRSpecialTypeCategory.VectorTypeDecl)) {
                smtemit.processVectorTypeDecl(edcl);
            }
            else if(edcl.specialDecls.has(MIRSpecialTypeCategory.ListTypeDecl)) {
                smtemit.processListTypeDecl(edcl);
            }
            else if(edcl.specialDecls.has(MIRSpecialTypeCategory.StackTypeDecl)) {
                smtemit.processStackTypeDecl(edcl);
            }
            else if(edcl.specialDecls.has(MIRSpecialTypeCategory.QueueTypeDecl)) {
                smtemit.processQueueTypeDecl(edcl);
            }
            else if(edcl.specialDecls.has(MIRSpecialTypeCategory.SetTypeDecl)) {
                smtemit.processSetTypeDecl(edcl);
            }
            else if(edcl.specialDecls.has(MIRSpecialTypeCategory.DynamicSetTypeDecl)) {
                smtemit.processDynamicSetTypeDecl(edcl);
            }
            else if(edcl.specialDecls.has(MIRSpecialTypeCategory.MapTypeDecl)) {
                smtemit.processMapTypeDecl(edcl);
            }
            else if(edcl.specialDecls.has(MIRSpecialTypeCategory.DynamicMapTypeDecl)) {
                smtemit.processDynamicMapTypeDecl(edcl);
            }
            else {
                if(edcl.ns === "NSCore" && edcl.name === "ISequence") {
                    smtemit.processISequenceTypeDecl(edcl);
                }
                else {
                    if(edcl.ns !== "NSCore" || BuiltinEntityDeclNames.find((be) => be[0] === edcl.name) === undefined) {
                        smtemit.processEntityDecl(edcl);
                    }
                }
            }
        });

        smtemit.bemitter.requiredSubtypeTagChecks.forEach((stc) => {
            const occ = stc.oftype.options[0] as MIRConceptType;
            for(let i = 0; i < occ.ckeys.length; ++i) {
                const atname = `AbstractTypeTag_${smtemit.temitter.getSMTTypeFor(smtemit.temitter.getMIRType(occ.ckeys[i]))}`;
                if(!smtemit.assembly.abstractTypes.includes(atname)) {
                    smtemit.assembly.abstractTypes.push(atname);
                }

                assembly.typeMap.forEach((mtype) => {
                    if(smtemit.temitter.isUniqueType(mtype) && assembly.subtypeOf(mtype, stc.t)) {
                        const ttag = `TypeTag_${smtemit.temitter.getSMTTypeFor(mtype)}`;

                        if(smtemit.assembly.subtypeRelation.find((ee) => ee.ttype === ttag && ee.atype === atname) === undefined) {
                            const issub = assembly.subtypeOf(mtype, stc.oftype);
                            smtemit.assembly.subtypeRelation.push({ttype: ttag, atype: atname, value: issub});
                        }
                    }
                });
            }
        });

        smtemit.bemitter.requiredIndexTagChecks.forEach((itc) => {
            const itag = `TupleIndexTag_${itc.idx}`;
            if(!smtemit.assembly.indexTags.includes(itag)) {
                smtemit.assembly.indexTags.push(itag);
            }

            assembly.typeMap.forEach((mtype) => {
                if (smtemit.temitter.isUniqueType(mtype) && assembly.subtypeOf(mtype, itc.oftype)) {
                    const ttype = mtype.options[0] as MIRTupleType;
                    const ttag = `TypeTag_${smtemit.temitter.getSMTTypeFor(mtype)}`;

                    if (smtemit.assembly.hasIndexRelation.find((ee) => ee.idxtag === itag && ee.atype === ttag) === undefined) {
                        const hasidx = itc.idx < ttype.entries.length;
                        smtemit.assembly.hasIndexRelation.push({ idxtag: itag, atype: ttag, value: hasidx });
                    }
                }
            });
        });

        smtemit.bemitter.requiredRecordTagChecks.forEach((rtc) => {
            const ptag = `RecordPropertyTag_${rtc.pname}`;
            if(!smtemit.assembly.propertyTags.includes(ptag)) {
                smtemit.assembly.propertyTags.push(ptag);
            }

            assembly.typeMap.forEach((mtype) => {
                if (smtemit.temitter.isUniqueType(mtype) && assembly.subtypeOf(mtype, rtc.oftype)) {
                    const ttype = mtype.options[0] as MIRRecordType;
                    const ttag = `TypeTag_${smtemit.temitter.getSMTTypeFor(mtype)}`;

                    if (smtemit.assembly.hasPropertyRelation.find((ee) => ee.pnametag === ptag && ee.atype === ttag) === undefined) {
                        const haspname = ttype.entries.find((entry) => entry.name === rtc.pname) !== undefined;
                        smtemit.assembly.hasPropertyRelation.push({ pnametag: ptag, atype: ttag, value: haspname });
                    }
                }
            });
        });

        assembly.tupleDecls.forEach((ttup) => {
            const mirtype = smtemit.temitter.getMIRType(ttup.trkey);
            const ttag = `TypeTag_${smtemit.temitter.getSMTTypeFor(mirtype)}`;
            const iskey = assembly.subtypeOf(mirtype, smtemit.temitter.getMIRType("NSCore::KeyType"));
            const isapi = assembly.subtypeOf(mirtype, smtemit.temitter.getMIRType("NSCore::APIType"));

            smtemit.assembly.typeTags.push(ttag);
            if(iskey) {
                smtemit.assembly.keytypeTags.push(ttag);
            }
            
            const smttype = smtemit.temitter.getSMTTypeFor(mirtype);
            const ops = smtemit.temitter.getSMTConstructorName(mirtype);
            const consargs = ttup.entries.map((entry, i) => {
                return { fname: smtemit.temitter.generateTupleIndexGetFunction(ttup, i), ftype: smtemit.temitter.getSMTTypeFor(entry.type) };
            });

            smtemit.assembly.tupleDecls.push(new SMTTupleDecl(iskey, isapi, smttype.name, ttag, { cname: ops.cons, cargs: consargs }, ops.box, ops.bfield));
        });

        assembly.recordDecls.forEach((trec) => {
            const mirtype = smtemit.temitter.getMIRType(trec.trkey);
            const ttag = `TypeTag_${smtemit.temitter.getSMTTypeFor(mirtype)}`;
            const iskey = assembly.subtypeOf(mirtype, smtemit.temitter.getMIRType("NSCore::KeyType"));
            const isapi = assembly.subtypeOf(mirtype, smtemit.temitter.getMIRType("NSCore::APIType"));

            smtemit.assembly.typeTags.push(ttag);
            if(iskey) {
                smtemit.assembly.keytypeTags.push(ttag);
            }
            
            const smttype = smtemit.temitter.getSMTTypeFor(mirtype);
            const ops = smtemit.temitter.getSMTConstructorName(mirtype);
            const consargs = trec.entries.map((entry) => {
                return { fname: smtemit.temitter.generateRecordPropertyGetFunction(trec, entry.name), ftype: smtemit.temitter.getSMTTypeFor(entry.type) };
            });

            smtemit.assembly.recordDecls.push(new SMTRecordDecl(iskey, isapi, smttype.name, ttag, { cname: ops.cons, cargs: consargs }, ops.box, ops.bfield));
        });

        assembly.ephemeralListDecls.forEach((ephl) => {
            const mirtype = smtemit.temitter.getMIRType(ephl.trkey);
            
            const smttype = smtemit.temitter.getSMTTypeFor(mirtype);
            const ops = smtemit.temitter.getSMTConstructorName(mirtype);
            const consargs = ephl.entries.map((entry, i) => {
                return { fname: smtemit.temitter.generateEphemeralListGetFunction(ephl, i), ftype: smtemit.temitter.getSMTTypeFor(entry) };
            });

            smtemit.assembly.ephemeralDecls.push(new SMTEphemeralListDecl(smttype.name, { cname: ops.cons, cargs: consargs }));
        });

        assembly.constantDecls.forEach((cdecl) => {
            const smtname = smtemit.temitter.mangle(cdecl.gkey);
            const consf = smtemit.temitter.mangle(cdecl.value);
            const ctype = smtemit.temitter.getSMTTypeFor(smtemit.temitter.getMIRType(cdecl.declaredType));
            smtemit.assembly.constantDecls.push(new SMTConstantDecl(smtname, ctype, consf));
        });

        smtemit.assembly.maskSizes = smtemit.bemitter.maskSizes;

        ////////////
        
        xxxx;

        const rrtype = typeemitter.getSMTTypeFor(typeemitter.getMIRType(entrypoint.resultType));

        let argscall: string[] = [];
        let argsdecls: string[] = [];
        for(let i = 0; i < entrypoint.params.length; ++i) {
            const param = entrypoint.params[i];
            const paramtype = typeemitter.getMIRType(param.type);

            argscall.push(`@${param.name}`);
            argsdecls.push(`(declare-const @${param.name} ${typeemitter.getSMTTypeFor(paramtype)})`);
            if(paramtype.options.length !== 1) {
                const tcops = paramtype.options.map((opt) => {
                    if(opt.trkey === "NSCore::None") {
                        return `(= @${param.name} bsqkey_none)`;
                    }
                    else if(opt.trkey === "NSCore::Bool") {
                        return `(is-bsqkey_bool @${param.name})`;
                    }
                    else if(opt.trkey === "NSCore::Int") {
                        return `(is-bsqkey_int @${param.name})`;
                    }
                    else {
                        return `(is-bsqkey_string @${param.name})`;
                    }
                });

                argsdecls.push(`(assert (or ${tcops.join(" ")}))`);
            }
        }

        if(entrypoint.preconditions !== undefined) {
            const params = entrypoint.params.map((param) => `@${param.name}`);
            argsdecls.push("(declare-const @icheck Result@Bool)")
            if(params.length === 0) {
                argsdecls.push(`(assert (= @icheck ${typeemitter.mangleStringForSMT(entrypoint.preconditions)}))`);
            }
            else {
                argsdecls.push(`(assert (= @icheck (${typeemitter.mangleStringForSMT(entrypoint.preconditions)} ${params.join(" ")})))`);
            }
            argsdecls.push("(assert (and (is-result_success@Bool @icheck) (result_success_value@Bool @icheck)))")
        }

        let conceptSubtypes: string[] = [];
        typeemitter.conceptSubtypeRelation.forEach((stv, cpt) => {
            const nemums = stv.map((ek) => `MIRNominalTypeEnum_${typeemitter.mangleStringForSMT(ek)}`).sort();
            if (nemums.length !== 0) {
                const sta = `(declare-const MIRConceptSubtypeArray$${typeemitter.mangleStringForSMT(cpt)} (Array Int Bool))`;
                let iv = "mirconceptsubtypearray_empty";
                for (let i = 0; i < nemums.length; ++i) {
                    iv = `(store ${iv} ${nemums[i]} true)`;
                }

                conceptSubtypes.push(sta + "\n" + `(assert (= MIRConceptSubtypeArray$${typeemitter.mangleStringForSMT(cpt)} ${iv}))`);
            }
        });

        const typechecks = [...bodyemitter.subtypeFMap].map(tcp => tcp[1]).sort((tc1, tc2) => tc1.order - tc2.order).map((tc) => tc.decl);

        let nominal_data_kinds: string[] = [];
        let special_name_decls: string[] = [];
        let ephdecls_fwd: string[] = [];
        let ephdecls: string[] = [];
        [...typeemitter.assembly.typeMap].forEach((te) => {
            const tt = te[1];

            if(typeemitter.typecheckIsName(tt, /^NSCore::None$/) || typeemitter.typecheckIsName(tt, /^NSCore::Bool$/) || typeemitter.typecheckIsName(tt, /^NSCore::Int$/) || typeemitter.typecheckIsName(tt, /^NSCore::BigInt$/) || typeemitter.typecheckIsName(tt, /^NSCore::Float64$/) 
            || typeemitter.typecheckIsName(tt, /^NSCore::String$/) || typeemitter.typecheckIsName(tt, /^NSCore::UUID$/) || typeemitter.typecheckIsName(tt, /^NSCore::LogicalTime$/) || typeemitter.typecheckIsName(tt, /^NSCore::CryptoHash$/) || typeemitter.typecheckIsName(tt, /^NSCore::ByteBuffer$/)
            || typeemitter.typecheckIsName(tt, /^NSCore::ISOTime$/) || typeemitter.typecheckIsName(tt, /^NSCore::Regex$/)) {
                        special_name_decls.push(`(assert (= MIRNominalTypeEnum_${tt.trkey.substr(8)} MIRNominalTypeEnum_${typeemitter.mangleStringForSMT(tt.trkey)}))`);
                    }
            
            if (tt.trkey === "NSCore::Tuple" || tt.trkey === "NSCore::Record") {
                special_name_decls.push(`(assert (= MIRNominalTypeEnum_${tt.trkey.substr(8)} MIRNominalTypeEnum_${typeemitter.mangleStringForSMT(tt.trkey)}))`);
            }

            if(tt.options.length === 1 && (tt.options[0] instanceof MIREntityType)) {
                const ndn = typeemitter.mangleStringForSMT(tt.trkey);
                const dk = typeemitter.generateInitialDataKindFlag(tt);
                nominal_data_kinds.push(`(assert (= (nominalDataKinds MIRNominalTypeEnum_${ndn}) ${dk.toString()}))`);
            }

            if(tt.options.length === 1 && (tt.options[0] instanceof MIREphemeralListType)) {
                const ephdecl = typeemitter.generateSMTEphemeral(tt.options[0] as MIREphemeralListType);
                ephdecls_fwd.push(ephdecl.fwddecl);
                ephdecls.push(ephdecl.fulldecl);
            }
        });

        let fulledecls = "";
        if(ephdecls_fwd.length !== 0) {
            fulledecls = "(declare-datatypes (\n"
            + `  ${ephdecls_fwd.sort().join("\n  ")}`
            + "\n) (\n"
            + `  ${ephdecls.sort().join("\n  ")}`
            + "\n))"
        }

        let constregexs: string[] = [];
        bodyemitter.allConstRegexes.forEach((v, k) => {
            constregexs.push(`;;${k} = ${v}`);
        });

        const resv = `(declare-const @smtres@ Result@${rrtype})`;
        const call = argscall.length !== 0 ? `(${bodyemitter.invokenameToSMT(entrypoint.key)} ${argscall.join(" ")})` : bodyemitter.invokenameToSMT(entrypoint.key);
        const cassert = `(assert (= @smtres@ ${call}))`;

        const bmcchk = `(assert (not (and (is-result_error@${rrtype} @smtres@) (is-result_bmc (result_error_code@${rrtype} @smtres@)))))`

        let chk = errorcheck || isverify ? `(assert (is-result_error@${rrtype} @smtres@))` : `(assert (not (is-result_error@${rrtype} @smtres@)))`;

        const callinfo = resv + "\n" + cassert + "\n" + bmcchk + "\n" + chk;

        return {
            NOMINAL_DECLS_FWD: typedecls_fwd.sort().join("\n    "),
            NOMINAL_CONSTRUCTORS: typedecls.sort().join("\n    "),
            NOMINAL_OBJECT_CONSTRUCTORS: ocons.sort().join("\n    "),
        
            NOMINAL_TYPE_KIND_DECLS: [...nominaltypeinfo, ...concepttypeinfo].join("\n"),
            NOMINAL_TYPE_TO_DATA_KIND_ASSERTS: nominal_data_kinds.sort().join("\n"),
            SPECIAL_NAME_BLOCK_ASSERTS: special_name_decls.sort().join("\n"),
        
            EPHEMERAL_DECLS: fulledecls,
        
            EMPTY_CONTENT_ARRAY_DECLS: edecls.sort().join("\n"),
        
            RESULTS_FWD: resultdecls_fwd.sort().join("\n    "),
            RESULTS: resultdecls.sort().join("\n    "),
        
            REGEX_DECLS: constregexs.sort().join("\n    "),

            CONCEPT_SUBTYPE_RELATION_DECLARE: conceptSubtypes.sort().join("\n"),
            SUBTYPE_DECLS: typechecks.join("\n    "),
        
            VFIELD_ACCESS: vfieldaccess.join("\n"),

            FUNCTION_DECLS: [...udecls, ...funcdecls, ...uaxioms].join("\n"),
            ARG_VALUES: argsdecls.join("\n"),
        
            INVOKE_ACTION: callinfo
        };
    }
}

export {
    SMTEmitter
};
