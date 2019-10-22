//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRRecordType, MIRInvokeDecl } from "../../compiler/mir_assembly";
import { CPPTypeEmitter } from "./cpptype_emitter";
import { CPPBodyEmitter } from "./cppbody_emitter";
import { NOT_IMPLEMENTED, sanitizeForCpp } from "./cpputils";
import { constructCallGraphInfo } from "../../compiler/mir_callg";
import { extractMirBodyKeyPrefix, extractMirBodyKeyData, MIRInvokeKey } from "../../compiler/mir_ops";

type CPPCode = {
    typedecls_fwd: string,
    typedecls: string,
    funcdecls_fwd: string,
    funcdecls: string,
    conststring_declare: string,
    conststring_create: string,
    propertyenums: string,
    propertynames: string
};

class CPPEmitter {
    static emit(assembly: MIRAssembly): CPPCode {
        const typeemitter = new CPPTypeEmitter(assembly);
        const bodyemitter = new CPPBodyEmitter(assembly, typeemitter);

        let typedecls_fwd: string[] = [];
        let typedecls: string[] = [];
        assembly.conceptDecls.forEach((cdecl) => {
            const cppdecl = typeemitter.generateCPPConcept(cdecl);
            if (cppdecl !== undefined) {
                typedecls_fwd.push(cppdecl.fwddecl);
                typedecls.push(cppdecl.fulldecl);
            }
        });
        assembly.entityDecls.forEach((edecl) => {
            const cppdecl = typeemitter.generateCPPEntity(edecl);
            if (cppdecl !== undefined) {
                typedecls_fwd.push(cppdecl.fwddecl);
                typedecls.push(cppdecl.fulldecl);
            }
        });

        const cginfo = constructCallGraphInfo(assembly.entryPoints, assembly);
        const rcg = [...cginfo.topologicalOrder].reverse();

        let funcdecls_fwd: string[] = [];
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
                    const finfo = bodyemitter.generateCPPInvoke(idcl);

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

        let conststring_declare: string[] = [];
        let conststring_create: string[] = [];
        bodyemitter.allConstStrings.forEach((v, k) => {
            conststring_declare.push(`static NSCore$cc$String ${v};`);
            conststring_create.push(`NSCore$cc$String Runtime::${v}(move(std::string(${k})), 1);`);
        });

        let propertyenums: Set<string> = new Set<string>();
        let propertynames: Set<string> = new Set<string>();
        bodyemitter.allPropertyNames.forEach((pname) => {
            propertyenums.add(sanitizeForCpp(pname));
            propertynames.add(`"${pname}"`);
        });
        assembly.typeMap.forEach((tt) => {
            tt.options.forEach((topt) => {
                if (topt instanceof MIRRecordType) {
                    topt.entries.forEach((entry) => {
                        propertyenums.add(sanitizeForCpp(entry.name));
                        propertynames.add(`"${entry.name}"`);
                    });
                }
            });
        });

        return {
            typedecls_fwd: typedecls_fwd.sort().join("\n"),
            typedecls: typedecls.sort().join("\n"),
            funcdecls_fwd: funcdecls_fwd.sort().join("\n"),
            funcdecls: funcdecls.sort().join("\n"),
            conststring_declare: conststring_declare.sort().join("\n  "),
            conststring_create: conststring_create.sort().join("\n  "),
            propertyenums: [...propertyenums].sort().join(",\n  "),
            propertynames: [...propertynames].sort().join(",\n  ")
        };
    }
}

export {
    CPPEmitter
};
