import { MIRInvokePrimitiveDecl, MIRType, MIREntityType, MIREntityTypeDecl, MIRPCode, MIRFunctionParameter } from "../../compiler/mir_assembly";
import { SMTLIBGenerator } from "./generator";

//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

type BuiltinTypeEmit = (tcstring: string, cstring: string) => [string, string?];
type BuiltinCallEmit = (smtgen: SMTLIBGenerator, inv: MIRInvokePrimitiveDecl, decl: string) => string;

const BuiltinCalls = new Map<string, BuiltinCallEmit>()
    .set("list_createofsize", (smtgen: SMTLIBGenerator, inv: MIRInvokePrimitiveDecl, decl: string) => {
        return "";
    })
    .set("list_empty", (smtgen: SMTLIBGenerator, inv: MIRInvokePrimitiveDecl, decl: string) => {
        const rcvrtype = smtgen.assembly.typeMap.get(inv.params[0].type) as MIRType;
        if (smtgen.isTypeExact(rcvrtype)) {
            return `${decl} (Result_Bool@result_success (= (${smtgen.typeToSMT2Constructor(rcvrtype)}@size this) 0)))`;
        }
        else {
            return `${decl} (Result_Bool@result_success (= (bsq_term_list_size this) 0)))`;
        }
    })
    .set("list_size", (smtgen: SMTLIBGenerator, inv: MIRInvokePrimitiveDecl, decl: string) => {
        const rcvrtype = smtgen.assembly.typeMap.get(inv.params[0].type) as MIRType;
        if (smtgen.isTypeExact(rcvrtype)) {
            return `${decl} (Result_Int@result_success (${smtgen.typeToSMT2Constructor(rcvrtype)}@size this)))`;
        }
        else {
            return `${decl} (Result_Int@result_success (bsq_term_list_size this)))`;
        }
    })

    .set("list_filter", (smtgen: SMTLIBGenerator, inv: MIRInvokePrimitiveDecl, decl: string) => {
        const rcvrtype = smtgen.assembly.typeMap.get(inv.params[0].type) as MIRType;
        const rtcons = smtgen.typeToSMT2Constructor(rcvrtype);
        const contentstype = (smtgen.assembly.entityDecls.get((rcvrtype.options[0] as MIREntityType).ekey) as MIREntityTypeDecl).terms.get("T") as MIRType;
        const restype = smtgen.assembly.typeMap.get(inv.resultType) as MIRType;
        const resulttype = "Result_" + smtgen.typeToSMT2Type(restype);

        const carray = `(Array Int ${smtgen.typeToSMT2Type(contentstype)})`;

        const pred = inv.pcodes.get("p") as MIRPCode;
        const cargs = pred.cargs.map((carg) => {
            const ptname = (inv.params.find((p) => p.name === carg) as MIRFunctionParameter).type;
            const ptype = smtgen.typeToSMT2Type(smtgen.assembly.typeMap.get(ptname) as MIRType);
            return `(${carg} ${ptype})`;
        });
        const rargs = `((size Int) (ina ${carray}) (i Int) (outa ${carray}) (j Int)${cargs.length !== 0 ? (" " + cargs.join(" ")) : ""})`;
        const passargs = cargs.length !== 0 ? (" " + cargs.join(" ")) : "";
        const pname = smtgen.invokenameToSMT2(pred.code);

        if (smtgen.isTypeExact(rcvrtype)) {
            const tbase = `
            (define-fun ${smtgen.invokenameToSMT2(inv.key)}0 ${rargs} ${resulttype}
                (${resulttype}@result_with_code (result_bmc ${inv.sourceLocation.line}))
            )
            `.trim();

            const tfun = `
            (define-fun ${smtgen.invokenameToSMT2(inv.key)}%k% ${rargs} ${resulttype}
                (ite (= size i)
                    (${resulttype}@result_success (${rtcons} j outa))
                    (ite (${pname} (select ina i)${passargs})
                        (${smtgen.invokenameToSMT2(inv.key)}%kdec% size ina (+ i 1) (store outa j (select ina i)) (+ j 1)${passargs})
                        (${smtgen.invokenameToSMT2(inv.key)}%kdec% size ina (+ i 1) outa j${passargs})
                    )
                )
            )
            `.trim();

            const tentry = `
            ${decl}
            (${smtgen.invokenameToSMT2(inv.key)}10 (${rtcons}@size this) (${rtcons}@contents this) 0 ${rtcons}@emptysingleton 0${passargs}))
            `.trim();

            return [tbase, ...[1, 2, 3, 4, 5, 6, 7, 8, 9, 10].map((i) => tfun.replace(/%k%/g, i.toString()).replace(/%kdec%/g, (i - 1).toString())), tentry].join("\n");
        }
        else {
            const tbase = `
            (define-fun ${smtgen.invokenameToSMT2(inv.key)}0 ${rargs} ${resulttype}
                (${resulttype}@result_with_code (result_bmc ${inv.sourceLocation.line}))
            )
            `.trim();

            const tfun = `
            (define-fun ${smtgen.invokenameToSMT2(inv.key)}%k% ${rargs} ${resulttype}
                (ite (= size i)
                    (${resulttype}@result_success (${rtcons} j outa))
                    (ite (${pname} (select ina i)${passargs})
                        (${smtgen.invokenameToSMT2(inv.key)}%kdec% size ina (+ i 1) (store outa j (select ina i)) (+ j 1)${passargs})
                        (${smtgen.invokenameToSMT2(inv.key)}%kdec% size ina (+ i 1) outa j${passargs})
                    )
                )
            )
            `.trim();

            const tentry = `
            ${decl}
            (${smtgen.invokenameToSMT2(inv.key)}10 (bsq_term_list_size this) (bsq_term_list_entries this) 0 ((as const (Array Int BTerm)) bsq_term_none) 0${passargs}))
            `.trim();

            return [tbase, ...[1, 2, 3, 4, 5, 6, 7, 8, 9, 10].map((i) => tfun.replace(/%k%/g, i.toString()).replace(/%kdec%/g, (i - 1).toString())), tentry].join("\n");
        }
    })

    .set("list_at", (smtgen: SMTLIBGenerator, inv: MIRInvokePrimitiveDecl, decl: string) => {
        const rcvrtype = smtgen.assembly.typeMap.get(inv.params[0].type) as MIRType;
        const iv = smtgen.varNameToSMT2Name(inv.params[1].name);
        const resulttype = "Result_" + smtgen.typeToSMT2Type(smtgen.assembly.typeMap.get(inv.resultType) as MIRType);

        if (smtgen.isTypeExact(rcvrtype)) {
            const rtcons = smtgen.typeToSMT2Constructor(rcvrtype);

            return `
            ${decl}
            (ite (and (<= 0 ${iv}) (< ${iv} (${rtcons}@size this)))
                (${resulttype}@result_success (select (${rtcons}@contents this) ${iv}))
                (${resulttype}@result_with_code (result_error ${inv.sourceLocation.pos})))
            )
            `;
        }
        else {
            return `
            ${decl}
            (ite (and (<= 0 ${iv}) (< ${iv} (bsq_term_list_size this)))
                (${resulttype}@result_success (select (bsq_term_list_entries this) ${iv}))
                (${resulttype}@result_with_code (result_error ${inv.sourceLocation.pos})))
            )
            `;
        }
    });

const BuiltinTypes = new Map<string, BuiltinTypeEmit>()
    .set("List", (tcstring: string, cstring: string) => {
        return [`    ((${tcstring} (${tcstring}@size Int) (${tcstring}@contents (Array Int ${cstring}))))`, `(declare-const ${tcstring}@emptysingleton (Array Int ${cstring}))`];
});

export { BuiltinTypeEmit, BuiltinTypes, BuiltinCallEmit, BuiltinCalls };
