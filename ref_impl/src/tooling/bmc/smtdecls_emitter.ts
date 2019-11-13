//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRInvokeDecl, MIRInvokeBodyDecl, MIREntityTypeDecl, MIRConstantDecl, MIRFieldDecl } from "../../compiler/mir_assembly";
import { SMTTypeEmitter } from "./smttype_emitter";
import { SMTBodyEmitter } from "./smtbody_emitter";
import { constructCallGraphInfo } from "../../compiler/mir_callg";
import { extractMirBodyKeyPrefix, extractMirBodyKeyData, MIRInvokeKey, MIRNominalTypeKey, MIRConstantKey, MIRFieldKey, MIRBodyKey } from "../../compiler/mir_ops";

import * as assert from "assert";

function NOT_IMPLEMENTED<T>(msg: string): T {
    throw new Error(`Not Implemented: ${msg}`);
}

type SMTCode = {
    typedecls_fwd: string,
    typedecls: string,
    fixedtupledecls_fwd: string,
    fixedtupledecls: string,
    fixedrecorddecls_fwd: string,
    fixedrecorddecls: string,
    resultdecls_fwd: string,
    resultdecls: string,
    function_decls: string,
    args_info: string,
    main_info: string
};

class SMTEmitter {
    static emit(assembly: MIRAssembly, entrypoint: MIRInvokeBodyDecl): SMTCode {
        const typeemitter = new SMTTypeEmitter(assembly);
        const bodyemitter = new SMTBodyEmitter(assembly, typeemitter);

        const cginfo = constructCallGraphInfo(assembly.entryPoints, assembly);
        const rcg = [...cginfo.topologicalOrder];

        let typedecls_fwd: string[] = [];
        let typedecls: string[] = [];
        assembly.entityDecls.forEach((edecl) => {
            const smtdecl = typeemitter.generateSMTEntity(edecl);
            if (smtdecl !== undefined) {
                typedecls_fwd.push(smtdecl.fwddecl);
                typedecls.push(smtdecl.fulldecl);
            }
        });

        let fixedtupledecls_fwd: string[] = [];
        let fixedtupledecls: string[] = [];
        let fixedrecorddecls_fwd: string[] = [];
        let fixedrecorddecls: string[] = [];
        assembly.typeMap.forEach((tt) => {
            if (typeemitter.isTupleType(tt) && SMTTypeEmitter.getTupleTypeMaxLength(tt) !== 0) {
                fixedtupledecls_fwd.push(`(${typeemitter.typeToSMTCategory(tt)} 0)`);

                const maxlen = SMTTypeEmitter.getTupleTypeMaxLength(tt);
                let cargs: string[] = [];
                for (let i = 0; i < maxlen; ++i) {
                    cargs.push(`(${typeemitter.generateTupleAccessor(tt, i)} bsqtuple_entry)`);
                }
                fixedtupledecls.push(`( (${typeemitter.generateTupleConstructor(tt)} ${cargs.join(" ")}) )`);
            }

            if (typeemitter.isRecordType(tt) && SMTTypeEmitter.getRecordTypeMaxPropertySet(tt).length !== 0) {
                fixedrecorddecls_fwd.push(`(${typeemitter.typeToSMTCategory(tt)} 0)`);

                const maxset = SMTTypeEmitter.getRecordTypeMaxPropertySet(tt);
                let cargs: string[] = [];
                for (let i = 0; i < maxset.length; ++i) {
                    cargs.push(`(${typeemitter.generateRecordAccessor(tt, maxset[i])} bsqrecord_entry)`);
                }
                fixedrecorddecls.push(`( (${typeemitter.generateRecordConstructor(tt)} ${cargs.join(" ")}) )`);
            }
        });

        let funcdecls: string[] = [];
        let resultdecls_fwd: string[] = [];
        let resultdecls: string[] = [];
        for (let i = 0; i < rcg.length; ++i) {
            const cn = rcg[i];

            const cscc = cginfo.recursive.find((scc) => scc.has(cn.invoke));
            let worklist = cscc !== undefined ? [...cscc].sort() : [cn.invoke];

            let lastgas = new Map<MIRBodyKey, number>();
            while (worklist.length !== 0) {
                const bbup = worklist.shift() as MIRBodyKey;

                let gas: number | undefined = undefined;
                let gasdown: number | undefined = undefined;
                let currentSCC = new Set<string>();
                if (cscc !== undefined) {
                    const gasctr = lastgas.get(bbup) || 1;
                    const cgas = bodyemitter.getGasForOperation(bbup);
                    if (gasctr <= cgas) {
                        gas = gasctr;
                        lastgas.set(bbup, gas + 1);
                    }

                    gasdown = gas !== undefined ? gas - 1 : cgas;

                    cscc.forEach((bc) => currentSCC.add(extractMirBodyKeyData(bc)));
                }

                const tag = extractMirBodyKeyPrefix(bbup);
                if (tag === "invoke") {
                    const ikey = extractMirBodyKeyData(bbup) as MIRInvokeKey;
                    const idcl = (assembly.invokeDecls.get(ikey) || assembly.primitiveInvokeDecls.get(ikey)) as MIRInvokeDecl;
                    const finfo = bodyemitter.generateSMTInvoke(idcl, currentSCC, gas, gasdown);

                    funcdecls.push(finfo);

                    const rtype = typeemitter.typeToSMTCategory(typeemitter.getMIRType(idcl.resultType));
                    if (!resultdecls_fwd.includes(`(Result@${rtype} 0)`)) {
                        resultdecls_fwd.push(`(Result@${rtype} 0)`);
                        resultdecls.push(`( (result_success@${rtype} (result_success_value@${rtype} ${rtype})) (result_error@${rtype} (result_error_code@${rtype} ErrorCode)) )`);
                    }
                }
                else if (tag === "pre") {
                    NOT_IMPLEMENTED<void>("Pre");
                }
                else if (tag === "post") {
                    NOT_IMPLEMENTED<void>("Post");
                }
                else if (tag === "invariant") {
                    const edcl = assembly.entityDecls.get(extractMirBodyKeyData(bbup) as MIRNominalTypeKey) as MIREntityTypeDecl;
                    funcdecls.push(bodyemitter.generateSMTInv(bbup, edcl));
                }
                else if (tag === "const") {
                    const cdcl = assembly.constantDecls.get(extractMirBodyKeyData(bbup) as MIRConstantKey) as MIRConstantDecl;
                    const cdeclemit = bodyemitter.generateSMTConst(bbup, cdcl);
                    if (cdeclemit !== undefined) {
                        funcdecls.push(cdeclemit);

                        const rtype = typeemitter.typeToSMTCategory(typeemitter.getMIRType(cdcl.declaredType));
                        if (!resultdecls_fwd.includes(`(Result@${rtype} 0)`)) {
                            resultdecls_fwd.push(`(Result@${rtype} 0)`);
                            resultdecls.push(`( (result_success@${rtype} (result_success_value@${rtype} ${rtype})) (result_error@${rtype} (result_error_code@${rtype} ErrorCode)) )`);
                        }
                    }

                }
                else {
                    assert(tag === "fdefault");

                    const fdcl = assembly.fieldDecls.get(extractMirBodyKeyData(bbup) as MIRFieldKey) as MIRFieldDecl;
                    const fdeclemit = bodyemitter.generateSMTFDefault(bbup, fdcl);
                    if (fdeclemit !== undefined) {
                        funcdecls.push(fdeclemit);

                        const rtype = typeemitter.typeToSMTCategory(typeemitter.getMIRType(fdcl.declaredType));
                        if (!resultdecls_fwd.includes(`(Result@${rtype} 0)`)) {
                            resultdecls_fwd.push(`(Result@${rtype} 0)`);
                            resultdecls.push(`( (result_success@${rtype} (result_success_value@${rtype} ${rtype})) (result_error@${rtype} (result_error_code@${rtype} ErrorCode)) )`);
                        }
                    }
                }

                if (gas !== undefined) {
                    worklist.push(bbup);
                }
            }
        }

        const rrtype = typeemitter.typeToSMTCategory(typeemitter.getMIRType(entrypoint.resultType));

        const resv = `(declare-const @smtres@ Result@${rrtype})`;
        const cassert = `(assert (= @smtres@ ${bodyemitter.invokenameToSMT(entrypoint.key)}))`;
        const chk = `(assert (is-result_error@${rrtype} @smtres@))`;

        const callinfo = resv + "\n" + cassert + "\n" + chk;

        return {
            typedecls_fwd: typedecls_fwd.sort().join("\n    "),
            typedecls: typedecls.sort().join("\n    "),
            fixedtupledecls_fwd: fixedtupledecls_fwd.sort().join("\n    "),
            fixedtupledecls: fixedtupledecls.sort().join("\n    "),
            fixedrecorddecls_fwd: fixedrecorddecls_fwd.sort().join("\n    "),
            fixedrecorddecls: fixedrecorddecls.sort().join("\n    "),
            resultdecls_fwd: resultdecls_fwd.sort().join("\n    "),
            resultdecls: resultdecls.sort().join("\n    "),
            function_decls: funcdecls.join("\n"),
            args_info: "",
            main_info: callinfo
        };
    }
}

export {
    SMTEmitter
};
