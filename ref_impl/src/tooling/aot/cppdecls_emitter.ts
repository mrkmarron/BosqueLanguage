//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRRecordType, MIRInvokeDecl, MIRConstantDecl, MIREntityTypeDecl, MIRFieldDecl } from "../../compiler/mir_assembly";
import { CPPTypeEmitter } from "./cpptype_emitter";
import { CPPBodyEmitter } from "./cppbody_emitter";
import { constructCallGraphInfo } from "../../compiler/mir_callg";
import { extractMirBodyKeyPrefix, extractMirBodyKeyData, MIRInvokeKey, MIRConstantKey, MIRNominalTypeKey, MIRFieldKey } from "../../compiler/mir_ops";

import * as assert from "assert";

function NOT_IMPLEMENTED<T>(msg: string): T {
    throw new Error(`Not Implemented: ${msg}`);
}

type CPPCode = {
    typedecls_fwd: string,
    typedecls: string,
    nominalenums: string,
    funcdecls_fwd: string,
    funcdecls: string,
    conststring_declare: string,
    conststring_create: string,
    propertyenums: string,
    fixedrecord_property_lists: string,
    propertynames: string,
    vfield_decls: string,
    vmethod_decls: string,
    entryname: string
};

class CPPEmitter {
    static emit(assembly: MIRAssembly, entrypoint: string): CPPCode {
        const typeemitter = new CPPTypeEmitter(assembly);
        const bodyemitter = new CPPBodyEmitter(assembly, typeemitter);

        let typedecls_fwd: string[] = [];
        let typedecls: string[] = [];
        let nominalenums: string[] = [];
        assembly.entityDecls.forEach((edecl) => {
            const cppdecl = typeemitter.generateCPPEntity(edecl);
            if (cppdecl !== undefined) {
                typedecls_fwd.push(cppdecl.fwddecl);
                typedecls.push(cppdecl.fulldecl);
                nominalenums.push(typeemitter.mangleStringForCpp(edecl.tkey));
            }
        });

        const cginfo = constructCallGraphInfo(assembly.entryPoints, assembly);
        const rcg = [...cginfo.topologicalOrder];

        let funcdecls_fwd: string[] = [];
        let funcdecls: string[] = [];
        for (let i = 0; i < rcg.length; ++i) {
            const bbup = rcg[i];
            const tag = extractMirBodyKeyPrefix(bbup.invoke);
            //
            //TODO: rec is implmented via stack recusion -- want to add option for bounded stack version
            //

            if (tag === "invoke") {
                const ikey = extractMirBodyKeyData(bbup.invoke) as MIRInvokeKey;
                const idcl = (assembly.invokeDecls.get(ikey) || assembly.primitiveInvokeDecls.get(ikey)) as MIRInvokeDecl;
                const finfo = bodyemitter.generateCPPInvoke(idcl);

                funcdecls_fwd.push(finfo.fwddecl);
                funcdecls.push(finfo.fulldecl);
            }
            else if (tag === "pre") {
                NOT_IMPLEMENTED<void>("Pre");
            }
            else if (tag === "post") {
                NOT_IMPLEMENTED<void>("Post");
            }
            else if (tag === "invariant") {
                const edcl = assembly.entityDecls.get(extractMirBodyKeyData(bbup.invoke) as MIRNominalTypeKey) as MIREntityTypeDecl;
                const finfo = bodyemitter.generateCPPInv(bbup.invoke, edcl);

                funcdecls_fwd.push(finfo.fwddecl);
                funcdecls.push(finfo.fulldecl);
            }
            else if (tag === "const") {
                const cdcl = assembly.constantDecls.get(extractMirBodyKeyData(bbup.invoke) as MIRConstantKey) as MIRConstantDecl;
                const finfo = bodyemitter.generateCPPConst(bbup.invoke, cdcl);

                if (finfo !== undefined) {
                    funcdecls_fwd.push(finfo.fwddecl);
                    funcdecls.push(finfo.fulldecl);
                }
            }
            else {
                assert(tag === "fdefault");
                const fdcl = assembly.fieldDecls.get(extractMirBodyKeyData(bbup.invoke) as MIRFieldKey) as MIRFieldDecl;
                const finfo = bodyemitter.generateCPPFDefault(bbup.invoke, fdcl);

                if (finfo !== undefined) {
                    funcdecls_fwd.push(finfo.fwddecl);
                    funcdecls.push(finfo.fulldecl);
                }
            }
        }

        let conststring_declare: string[] = [];
        let conststring_create: string[] = [];
        bodyemitter.allConstStrings.forEach((v, k) => {
            conststring_declare.push(`static BSQString ${v};`);
            conststring_create.push(`BSQString Runtime::${v}(move(std::string(${k})), 1);`);
        });

        let propertyenums: Set<string> = new Set<string>();
        let propertynames: Set<string> = new Set<string>();
        let fixedrecord_property_lists: Set<string> = new Set<string>();
        bodyemitter.allPropertyNames.forEach((pname) => {
            propertyenums.add(pname);
            propertynames.add(`"${pname}"`);
        });
        assembly.typeMap.forEach((tt) => {
            tt.options.forEach((topt) => {
                if (topt instanceof MIRRecordType) {
                    topt.entries.forEach((entry) => {
                        propertyenums.add(entry.name);
                        propertynames.add(`"${entry.name}"`);
                    });
                }
            });
        });

        return {
            typedecls_fwd: typedecls_fwd.sort().join("\n"),
            typedecls: typedecls.sort().join("\n"),
            nominalenums: nominalenums.sort().join(",\n    "),
            funcdecls_fwd: funcdecls_fwd.join("\n"),
            funcdecls: funcdecls.join("\n"),
            conststring_declare: conststring_declare.sort().join("\n  "),
            conststring_create: conststring_create.sort().join("\n  "),
            propertyenums: [...propertyenums].sort().join(",\n  "),
            fixedrecord_property_lists: [...fixedrecord_property_lists].sort().join("\n  "),
            propertynames: [...propertynames].sort().join(",\n  "),
            vfield_decls: "//NOT IMPLEMENTED YET -- NEED TO UPDATE MIR TO DO EXACT V-FIELD RESOLUTION",
            vmethod_decls: "//NOT IMPLEMENTED YET -- NEED TO UPDATE MIR TO DO EXACT V-METHOD RESOLUTION",
            entryname: typeemitter.mangleStringForCpp(entrypoint)
        };
    }
}

export {
    CPPEmitter
};
