//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRRecordType, MIRInvokeDecl, MIRInvokeBodyDecl, MIREphemeralListType } from "../../compiler/mir_assembly";
import { CPPTypeEmitter } from "./cpptype_emitter";
import { CPPBodyEmitter } from "./cppbody_emitter";
import { constructCallGraphInfo } from "../../compiler/mir_callg";

type CPPCode = {
    STATIC_STRING_DECLARE: string,
    STATIC_STRING_CREATE: string,

    STATIC_INT_DECLARE: string,
    STATIC_INT_CREATE: string,
    
    TYPEDECLS_FWD: string,
    TYPEDECLS: string,
    EPHEMERAL_LIST_DECLARE: string,

    PROPERTY_ENUM_DECLARE: string, 
    NOMINAL_TYPE_ENUM_DECLARE: string,

    PROPERTY_NAMES: string,
    NOMINAL_TYPE_DISPLAY_NAMES: string,

    CONCEPT_SUBTYPE_RELATION_DECLARE: string,
    NOMINAL_TYPE_TO_DATA_KIND: string,

    SPECIAL_NAME_BLOCK_BEGIN: string,

    VFIELD_ACCESS: string,
    
    TYPECHECKS: string,
    FUNC_DECLS_FWD: string,
    FUNC_DECLS: string,

    MAIN_CALL: string
};

class CPPEmitter {
    static emit(assembly: MIRAssembly, entrypointname: string): CPPCode {
        const typeemitter = new CPPTypeEmitter(assembly);
        typeemitter.initializeConceptSubtypeRelation();

        const bodyemitter = new CPPBodyEmitter(assembly, typeemitter);
        
        let typedecls_fwd: string[] = [];
        let typedecls: [string, string[]][] = [];
        let nominaltypeinfo: {enum: string, display: string, datakind: string}[] = [];
        let vfieldaccesses: string[] = [];
        [...assembly.entityDecls]
        .sort((a, b) => a[0]
        .localeCompare(b[0])).map((ee) => ee[1])
        .forEach((edecl) => {
            const cppdecl: any = typeemitter.generateCPPEntity(edecl);
            if (cppdecl !== undefined) {
                if(cppdecl.isref) {
                    const refdecl = cppdecl as { fwddecl: string, fulldecl: string };
                    typedecls_fwd.push(refdecl.fwddecl);
                    typedecls.push([refdecl.fulldecl, []]);
                }
                else {
                    const structdecl = cppdecl as { depon: string[], fwddecl: string, fulldecl: string, boxeddecl: string, ops: string[] };

                    typedecls_fwd.push(structdecl.fwddecl);
                    typedecls.push([structdecl.fulldecl + structdecl.ops.join("\n"), structdecl.depon]);
                    typedecls.push([structdecl.boxeddecl, [structdecl.fulldecl]]);

                    //
                    //TODO: buildup ops for STATIC_OPS_DECLARE, NOMINAL_TYPE_TO_OPS, and STATIC_OPS_CREATE
                    //
                }
            }

            const ereprk = typeemitter.getCPPReprFor(typeemitter.getMIRType(edecl.tkey));
            const enumv = `${typeemitter.mangleStringForCpp(edecl.tkey)} = BUILD_MIR_NOMINAL_TYPE(${ereprk.categoryinfo}, ${nominaltypeinfo.length + 1})`;
            const displayv = `U"${edecl.tkey}"`;
            const dk = typeemitter.generateInitialDataKindFlag(typeemitter.getMIRType(edecl.tkey));

            nominaltypeinfo.push({ enum: enumv, display: displayv, datakind: dk });

            edecl.fields.forEach((fd) => {
                if (fd.enclosingDecl !== edecl.tkey) {
                    const rftype = typeemitter.getCPPReprFor(typeemitter.getMIRType(fd.declaredType)).std;
                    const isig = `virtual ${rftype} get$${typeemitter.mangleStringForCpp(fd.fkey)}() { printf("%s\\n", "Bad v-field resolve -- ${fd.fkey}"); exit(1); ${rftype} res; return res; }`;

                    if (!vfieldaccesses.includes(isig)) {
                        vfieldaccesses.push(isig);
                    }
                }
            });
        });

        let concepttypeinfo: {enum: string, display: string, datakind: string}[] = [];
        [...assembly.conceptDecls]
        .sort((a, b) => a[0]
        .localeCompare(b[0])).map((ce) => ce[1])
        .forEach((cdecl) => {
            const enumv = `${typeemitter.mangleStringForCpp(cdecl.tkey)} = BUILD_MIR_NOMINAL_TYPE(MIRNominalTypeEnum_Category_Empty, ${concepttypeinfo.length + nominaltypeinfo.length + 1})`;
            const displayv = `U"${cdecl.tkey}"`;
            concepttypeinfo.push({ enum: enumv, display: displayv, datakind: "-1" });
        });
        
        const cginfo = constructCallGraphInfo(assembly.entryPoints, assembly);
        const rcg = [...cginfo.topologicalOrder].reverse();

        let funcdecls_fwd: string[] = [];
        let funcdecls: string[] = [];
        for (let i = 0; i < rcg.length; ++i) {
            const ikey = rcg[i].invoke;
            //
            //TODO: rec is implmented via stack recusion -- want to add option for bounded stack version
            //

            const idcl = (assembly.invokeDecls.get(ikey) || assembly.primitiveInvokeDecls.get(ikey)) as MIRInvokeDecl;
            const finfo = bodyemitter.generateCPPInvoke(idcl);

            funcdecls_fwd.push(finfo.fwddecl);
            funcdecls.push(finfo.fulldecl);
        }

        let conceptSubtypes: string[] = [];
        typeemitter.conceptSubtypeRelation.forEach((stv, cpt) => {
            const nemums = stv.map((ek) => `MIRNominalTypeEnum::${typeemitter.mangleStringForCpp(ek)}`).sort();
            if (nemums.length !== 0) {
                const sta = `constexpr MIRNominalTypeEnum MIRConceptSubtypeArray__${typeemitter.mangleStringForCpp(cpt)}[${nemums.length}] = {${nemums.join(", ")}};`;
                conceptSubtypes.push(sta);
            }
        });

        const typechecks = [...bodyemitter.subtypeFMap].map(tcp => tcp[1]).sort((tc1, tc2) => tc1.order - tc2.order).map((tc) => tc.decl);

        let special_name_decls: string[] = [];
        let ephdecls: string[] = [];
        [...typeemitter.assembly.typeMap].forEach((te) => {
            const tt = te[1];

            if(typeemitter.typecheckIsName(tt, /^NSCore::None$/) || typeemitter.typecheckIsName(tt, /^NSCore::Bool$/) || typeemitter.typecheckIsName(tt, /^NSCore::Int$/) || typeemitter.typecheckIsName(tt, /^NSCore::BigInt$/) || typeemitter.typecheckIsName(tt, /^NSCore::Float64$/) 
                    || typeemitter.typecheckIsName(tt, /^NSCore::String$/) || typeemitter.typecheckIsName(tt, /^NSCore::UUID$/) || typeemitter.typecheckIsName(tt, /^NSCore::LogicalTime$/) || typeemitter.typecheckIsName(tt, /^NSCore::CryptoHash$/) || typeemitter.typecheckIsName(tt, /^NSCore::ByteBuffer$/)
                    || typeemitter.typecheckIsName(tt, /^NSCore::ISOTime$/) || typeemitter.typecheckIsName(tt, /^NSCore::Regex$/)) {
                        special_name_decls.push(`#define MIRNominalTypeEnum_${tt.trkey.substr(8)} MIRNominalTypeEnum::${typeemitter.mangleStringForCpp(tt.trkey)}`);
                    }

            if(tt.trkey === "NSCore::Tuple" || tt.trkey === "NSCore::Record") {
                special_name_decls.push(`#define MIRNominalTypeEnum_${tt.trkey.substr(8)} MIRNominalTypeEnum::${typeemitter.mangleStringForCpp(tt.trkey)}`);
            }

            if(tt.options.length === 1 && (tt.options[0] instanceof MIREphemeralListType)) {
                const ephdecl = typeemitter.generateCPPEphemeral(tt.options[0] as MIREphemeralListType);
                ephdecls.push(ephdecl);
            }
        });

        let vfieldaccess: string[] = [];
        for(let i = 0; i < bodyemitter.vfieldLookups.length; ++i) {
            //
            //TODO: generate vfield switches
            //
        }

        //
        //TODO: need to process virtual bulk data operations -- also see SMT versions
        //
        if(bodyemitter.vfieldProjects.length !== 0 || bodyemitter.vfieldUpdates.length !== 0 || bodyemitter.vobjmerges.length !== 0) {
            console.log("NOT IMPLEMENTED -- virtual bulk operators for nominal types");
            process.exit(1);
        }

        let conststring_declare: string[] = [];
        let conststring_create: string[] = [];
        bodyemitter.allConstStrings.forEach((v, k) => {
            conststring_declare.push(`static BSQString ${v};`);
            conststring_create.push(`BSQString Runtime::${v}(${k}, 1);`);
        });

        let constint_declare: string[] = [];
        let constint_create: string[] = [];
        bodyemitter.allConstBigInts.forEach((v, k) => {
            constint_declare.push(`static BSQInt ${v};`);
            constint_create.push(`BSQInt Runtime::${v}(BigInt(${k}));`);
        });

        let propertyenums: Set<string> = new Set<string>();
        let propertynames: Set<string> = new Set<string>();
        bodyemitter.allPropertyNames.forEach((pname) => {
            propertyenums.add(pname);
            propertynames.add(`U"${pname}"`);
        });
        assembly.typeMap.forEach((tt) => {
            tt.options.forEach((topt) => {
                if (topt instanceof MIRRecordType) {
                    topt.entries.forEach((entry) => {
                        propertyenums.add(entry.name);
                        propertynames.add(`U"${entry.name}"`);
                    });
                }
            });
        });

        //
        //TODO: need to provide parse for API types and link in here
        //
        const entrypoint = assembly.invokeDecls.get(entrypointname) as MIRInvokeBodyDecl;
        const restype = typeemitter.getMIRType(entrypoint.resultType);
        const mainsig = `int main(int argc, char** argv)`;
        const chkarglen = `    if(argc != ${entrypoint.params.length} + 1) { fprintf(stderr, "Expected ${entrypoint.params.length} arguments but got %i\\n", argc - 1); exit(1); }`;
        const convdecl = "    std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;";
        const convargs = entrypoint.params.map((p, i) => {
            if(p.type === "NSCore::Bool") {
                const fchk = `if(std::string(argv[${i}+1]) != "true" && std::string(argv[${i}+1]) != "false") { fprintf(stderr, "Bad argument for ${p.name} -- expected Bool got %s\\n", argv[${i}+1]); exit(1); }`;
                const conv = `bool ${p.name} = std::string(argv[${i}+1]) == "true";`;
                return "    " + fchk + "\n    " + conv;
            }
            else if(p.type === "NSCore::Int") {
                const fchk = `if(!std::regex_match(std::string(argv[${i}+1]), std::regex("^([+]|[-])?[0-9]{1,8}$"))) { fprintf(stderr, "Bad argument for ${p.name} -- expected (small) Int got %s\\n", argv[${i}+1]); exit(1); }`;
                const conv = `int64_t ${p.name} = std::stoi(std::string(argv[${i}+1]));`;
                return "    \n    " + fchk + "\n    " + conv;
            } 
            else  {
                const conv = `BSQString ${p.name}(argv[${i}+1], 1);`;
                return "    " + conv;
            }
        });

        let scopev = "";
        const scopevar = bodyemitter.varNameToCppName("$scope$");

        let callargs = entrypoint.params.map((p) => p.type !== "NSCore::String" ? p.name : `&${p.name}`);
        const resrc = typeemitter.getRefCountableStatus(restype);
        if (resrc !== "no") {
            scopev = `BSQRefScope ${scopevar};`;
            callargs.push(scopevar);
        }        
        const callv = `${bodyemitter.invokenameToCPP(entrypointname)}(${callargs.join(", ")})`;
        const fcall = `std::cout << conv.to_bytes(diagnostic_format(${typeemitter.coerce(callv, restype, typeemitter.anyType)})) << "\\n"`;

        const maincall = `${mainsig} {\n${chkarglen}\n\n${convdecl}\n${convargs.join("\n")}\n\n  try {\n    ${scopev}\n    ${fcall};\n    fflush(stdout);\n    return 0;\n  } catch (BSQAbort& abrt) HANDLE_BSQ_ABORT(abrt) \n}\n`;


        return {
            STATIC_STRING_DECLARE: conststring_declare.sort().join("\n  "),
            STATIC_STRING_CREATE: conststring_create.sort().join("\n  "),
        
            STATIC_INT_DECLARE: constint_declare.sort().join("\n  "),
            STATIC_INT_CREATE: constint_create.sort().join("\n  "),
            
            TYPEDECLS_FWD: typedecls_fwd.sort().join("\n"),
            TYPEDECLS: typedecls.map((tde) => tde[0]).sort().join("\n"),
            EPHEMERAL_LIST_DECLARE: ephdecls.sort().join("\n"),
        
            PROPERTY_ENUM_DECLARE: [...propertyenums].sort().join(",\n  "), 
            NOMINAL_TYPE_ENUM_DECLARE: [...nominaltypeinfo, ...concepttypeinfo].map((nti) => nti.enum).join(",\n    "),
        
            PROPERTY_NAMES: [...propertynames].sort().join(",\n  "),
            NOMINAL_TYPE_DISPLAY_NAMES: [...nominaltypeinfo, ...concepttypeinfo].map((nti) => `${nti.display}`).join(",\n  "),
        
            CONCEPT_SUBTYPE_RELATION_DECLARE: conceptSubtypes.sort().join("\n"),
            NOMINAL_TYPE_TO_DATA_KIND: [...nominaltypeinfo].map((nti) => nti.datakind).join(",\n    "),
        
            SPECIAL_NAME_BLOCK_BEGIN: special_name_decls.sort().join("\n"),

            VFIELD_ACCESS: vfieldaccess.sort().join("\n"),

            TYPECHECKS: typechecks.join("\n"),
            FUNC_DECLS_FWD: funcdecls_fwd.join("\n"),
            FUNC_DECLS: funcdecls.join("\n"),
        
            MAIN_CALL: maincall
        };
    }
}

export {
    CPPEmitter
};
