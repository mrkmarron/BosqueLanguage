//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRRecordType } from "../../compiler/mir_assembly";
import { CPPTypeEmitter } from "./cpptype_emitter";
import { CPPBodyEmitter } from "./cppbody_emitter";
import { NOT_IMPLEMENTED, sanitizeForCpp } from "./cpputils";

type cppcode = {
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
    static emit(assembly: MIRAssembly): cppcode {
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

        let funcdecls_fwd: string[] = [];
        let funcdecls: string[] = [];
        assembly.primitiveInvokeDecls.forEach((cdecl) => {
            NOT_IMPLEMENTED<string>("Primitive Invoke");
        });
        assembly.invokeDecls.forEach((fdecl) => {
            const cppdecl = bodyemitter.generateInvoke(fdecl);
            if (cppdecl !== undefined) {
                funcdecls_fwd.push(cppdecl.fwddecl);
                funcdecls.push(cppdecl.fulldecl);
            }
        });

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
