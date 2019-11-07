//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRInvokeDecl, MIRInvokeBodyDecl, MIREntityTypeDecl, MIRConstantDecl, MIRFieldDecl } from "../../compiler/mir_assembly";
import { SMTTypeEmitter } from "./smttype_emitter";
import { SMTBodyEmitter } from "./smtbody_emitter";
import { constructCallGraphInfo } from "../../compiler/mir_callg";
import { NOT_IMPLEMENTED, sanitizeStringForSMT } from "./smtutils";
import { extractMirBodyKeyPrefix, extractMirBodyKeyData, MIRInvokeKey, MIRNominalTypeKey, MIRConstantKey, MIRFieldKey } from "../../compiler/mir_ops";

import * as assert from "assert";

type SMTCode = {
    typedecls_fwd: string,
    typedecls: string,
    fixedtupledecls_fwd: string,
    fixedtupledecls: string,
    fixedrecorddecls_fwd: string,
    fixedrecorddecls: string,
    resultdecls_fwd: string,
    resultdecls: string,
    function_decls: string
};

class SMTEmitter {
    static emit(assembly: MIRAssembly): SMTCode {
        const typeemitter = new SMTTypeEmitter(assembly);
        const bodyemitter = new SMTBodyEmitter(assembly, typeemitter);

        const cginfo = constructCallGraphInfo(assembly.entryPoints, assembly);
        const rcg = [...cginfo.topologicalOrder];

        let typedecls_fwd: string[] = [];
        let typedecls: string[] = [];
        let resultdecls_fwd: string[] = [];
        let resultdecls: string[] = [];
        assembly.entityDecls.forEach((edecl) => {
            const smtdecl = typeemitter.generateSMTEntity(edecl);
            if (smtdecl !== undefined) {
                typedecls_fwd.push(smtdecl.fwddecl);
                typedecls.push(smtdecl.fulldecl);

                resultdecls_fwd.push(`(Result@${sanitizeStringForSMT(edecl.tkey)} 0)`);
                resultdecls.push(`( (result_success$${sanitizeStringForSMT(edecl.tkey)} (result_success_value@${sanitizeStringForSMT(edecl.tkey)} ${sanitizeStringForSMT(edecl.tkey)})) (result_error@${sanitizeStringForSMT(edecl.tkey)} (result_error_code@${sanitizeStringForSMT(edecl.tkey)} ErrorCode)) )`);
            }
        });

        let fixedtupledecls_fwd: string[] = [];
        let fixedtupledecls: string[] = [];
        let fixedrecorddecls_fwd: string[] = [];
        let fixedrecorddecls: string[] = [];
        assembly.typeMap.forEach((tt) => {
            if (typeemitter.isFixedTupleType(tt) && SMTTypeEmitter.getFixedTupleType(tt).entries.length !== 0) {
                fixedtupledecls_fwd.push(`(${typeemitter.typeToSMTCategory(tt)} 0)`);

                const cargs = (SMTTypeEmitter.getFixedTupleType(tt)).entries.map((entry, i) => {
                    return `(${typeemitter.generateFixedTupleAccessor(tt, i)} BTerm)`;
                });
                fixedtupledecls.push(`( (${typeemitter.generateFixedTupleConstructor(tt)} ${cargs.join(" ")}) )`);
            }

            if (typeemitter.isFixedRecordType(tt) && SMTTypeEmitter.getFixedRecordType(tt).entries.length !== 0) {
                fixedrecorddecls_fwd.push(`(${typeemitter.typeToSMTCategory(tt)} 0)`);

                const cargs = (SMTTypeEmitter.getFixedRecordType(tt)).entries.map((entry) => {
                    return `(${typeemitter.generateFixedRecordAccessor(tt, entry.name)} BTerm)`;
                });
                fixedrecorddecls.push(`( (${typeemitter.generateFixedRecordConstructor(tt)} ${cargs.join(" ")}) )`);
            }
        });

        let funcdecls: string[] = [];
        for (let i = 0; i < rcg.length; ++i) {
            const bbup = rcg[i];
            if (cginfo.recursive.findIndex((scc) => scc.has(bbup.invoke)) !== -1) {
                NOT_IMPLEMENTED<void>("Recursive Invoke");
            }
            else {
                const tag = extractMirBodyKeyPrefix(bbup.invoke);
                if (tag === "invoke") {
                    const ikey = extractMirBodyKeyData(bbup.invoke) as MIRInvokeKey;
                    const idcl = (assembly.invokeDecls.get(ikey) || assembly.primitiveInvokeDecls.get(ikey)) as MIRInvokeDecl;
                    const finfo = bodyemitter.generateSMTInvoke(idcl, 0);

                    funcdecls.push(finfo);
                }
                else if (tag === "pre") {
                    NOT_IMPLEMENTED<void>("Pre");
                }
                else if (tag === "post") {
                    NOT_IMPLEMENTED<void>("Post");
                }
                else if (tag === "invariant") {
                    const edcl = assembly.entityDecls.get(extractMirBodyKeyData(bbup.invoke) as MIRNominalTypeKey) as MIREntityTypeDecl;
                    funcdecls.push(bodyemitter.generateSMTInv(bbup.invoke, edcl));
                }
                else if (tag === "const") {
                    const cdcl = assembly.constantDecls.get(extractMirBodyKeyData(bbup.invoke) as MIRConstantKey) as MIRConstantDecl;
                    const cdeclemit = bodyemitter.generateSMTConst(bbup.invoke, cdcl);
                    if (cdeclemit !== undefined) {
                        funcdecls.push(cdeclemit);
                    }

                }
                else {
                    assert(tag === "fdefault");

                    const fdcl = assembly.fieldDecls.get(extractMirBodyKeyData(bbup.invoke) as MIRFieldKey) as MIRFieldDecl;
                    const fdeclemit = bodyemitter.generateSMTFDefault(bbup.invoke, fdcl);
                    if (fdeclemit !== undefined) {
                        funcdecls.push(fdeclemit);
                    }
                }
            }
        }

        return {
            typedecls_fwd: typedecls_fwd.sort().join("\n"),
            typedecls: typedecls.sort().join("\n"),
            fixedtupledecls_fwd: fixedtupledecls_fwd.sort().join("\n"),
            fixedtupledecls: fixedtupledecls.sort().join("\n"),
            fixedrecorddecls_fwd: fixedrecorddecls_fwd.sort().join("\n"),
            fixedrecorddecls: fixedrecorddecls.sort().join("\n"),
            resultdecls_fwd: resultdecls_fwd.sort().join("\n"),
            resultdecls: resultdecls.sort().join("\n"),
            function_decls: funcdecls.join("\n")
        };
    }

    static emitEntrypointCall(assembly: MIRAssembly, entrypoint: MIRInvokeBodyDecl): { arginfo: string, callinfo: string } {
        const typeemitter = new SMTTypeEmitter(assembly);
        const bodyemitter = new SMTBodyEmitter(assembly, typeemitter);

        const rrtype = typeemitter.typeToSMTCategory(typeemitter.getMIRType(entrypoint.resultType));

        const resv = `(declare-const @smtres@ Result@${rrtype})`;
        const cassert = `(assert (= @smtres@ ${bodyemitter.invokenameToSMT(entrypoint.key)}))`;
        const chk = `(assert (is-result_error@${rrtype} @smtres@))`;

        const callinfo = resv + "\n" + cassert + "\n" + chk;

        return {
            arginfo: "",
            callinfo: callinfo
        };
    }
}

export {
    SMTEmitter
};
