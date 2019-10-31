//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRInvokeDecl, MIRInvokeBodyDecl } from "../../compiler/mir_assembly";
import { SMTTypeEmitter } from "./smttype_emitter";
import { SMTBodyEmitter } from "./smtbody_emitter";
import { constructCallGraphInfo } from "../../compiler/mir_callg";
import { NOT_IMPLEMENTED, sanitizeStringForSMT } from "./smtutils";
import { extractMirBodyKeyPrefix, extractMirBodyKeyData, MIRInvokeKey } from "../../compiler/mir_ops";

type SMTCode = {
    typedecls_fwd: string,
    typedecls_boxed: string,
    typedecls: string,
    resultdecls_fwd: string,
    resultdecls: string,
    function_decls: string
};

class SMTEmitter {
    static emit(assembly: MIRAssembly): SMTCode {
        const typeemitter = new SMTTypeEmitter(assembly);
        const bodyemitter = new SMTBodyEmitter(assembly, typeemitter);

        const cginfo = constructCallGraphInfo(assembly.entryPoints, assembly);
        const rcg = [...cginfo.topologicalOrder].reverse();

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

                    funcdecls.push(...finfo.supportcalls, finfo.fulldecl);
                }
                else if (tag === "pre") {
                    NOT_IMPLEMENTED<void>("Pre");
                }
                else if (tag === "post") {
                    NOT_IMPLEMENTED<void>("Post");
                }
                else if (tag === "invariant") {
                    NOT_IMPLEMENTED<void>("Invariant");
                }
                else if (tag === "const") {
                    NOT_IMPLEMENTED<void>("Const");
                }
                else {
                    NOT_IMPLEMENTED<void>("Field Default");
                }
            }
        }

        return {
            typedecls_fwd: typedecls_fwd.sort().join("\n"),
            typedecls: typedecls.sort().join("\n"),
            typedecls_boxed: typedecls.sort().join("\n"),
            resultdecls_fwd: resultdecls_fwd.sort().join("\n"),
            resultdecls: resultdecls.sort().join("\n"),
            function_decls: funcdecls.sort().join("\n")
        };
    }

    static emitEntrypointCall(assembly: MIRAssembly, entrypoint: MIRInvokeBodyDecl): { arginfo: string, callinfo: string } {
        const typeemitter = new SMTTypeEmitter(assembly);
        const bodyemitter = new SMTBodyEmitter(assembly, typeemitter);

        const rrtype = typeemitter.typeToSMTCategory(typeemitter.getMIRType(entrypoint.resultType));

        const resv = `(declare-const @smtres@ Result$${rrtype})`;
        const cassert = `(assert (= @smtres@ ${bodyemitter.invokenameToSMT(entrypoint.key)}))`;
        const chk = `(assert (is-result_error$${rrtype} @smtres@))`;

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
