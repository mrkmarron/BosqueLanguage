//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly } from "../../compiler/mir_assembly";
import { CPPTypeEmitter } from "./cpptype_emitter";
import { CPPBodyEmitter } from "./cppbody_emitter";
import { NOT_IMPLEMENTED } from "./cpputils";

type cppcode = {
    typedecls_fwd: string,
    typedecls: string,
    funcdecls_fwd: string,
    funcdecls: string,
    conststring_declare: string,
    conststring_create: string
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

        });

        return {
            typedecls_fwd: typedecls_fwd.sort().join(""),
            typedecls: typedecls.sort().join("\n\n"),
            funcdecls_fwd: funcdecls_fwd.sort().join(""),
            funcdecls: funcdecls.sort().join("\n\n"),
        };
    }
}

export {
    CPPEmitter
};
