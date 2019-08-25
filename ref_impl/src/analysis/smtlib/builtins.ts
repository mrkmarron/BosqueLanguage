import { MIRInvokePrimitiveDecl, MIRType } from "../../compiler/mir_assembly";
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
        const iv = smtgen.varNameToSMT2Name(inv.params[1].name);
        const restype = smtgen.assembly.typeMap.get(inv.resultType) as MIRType;
        const resulttype = "Result_" + smtgen.typeToSMT2Type(restype);

        if (smtgen.isTypeExact(rcvrtype)) {
            const ltype = smtgen.typeToSMT2Type(rcvrtype);
            const constype = smtgen.typeToSMT2Constructor(rcvrtype);

            const tbase = `
            (define-fun ${smtgen.invokenameToSMT2(inv.key)}0 ((l ${ltype}) (i Int)) ${resulttype}
                (ite (= i 0) (${resulttype}@result_success (${constype}@h l)) (${resulttype}@result_with_code (result_bmc ${inv.sourceLocation.line})))
            )
            `.trim();

            const tfun = `
            (define-fun ${smtgen.invokenameToSMT2(inv.key)}%k% ((l ${ltype}) (i Int)) ${resulttype}
                (ite (= i 0) (${resulttype}@result_success (${constype}@h l)) (${smtgen.invokenameToSMT2(inv.key)}%kdec% l (- i 1)))
            )
            `.trim();

            const tentry = `
            ${decl}
            (ite (and (<= 0 ${iv}) (< ${iv} (${constype}@size this)))
                (${smtgen.invokenameToSMT2(inv.key)}9 this ${iv})
                (${resulttype}@result_with_code (result_error ${inv.sourceLocation.pos})))
            )
            `.trim();

            return [tbase, ...[1, 2, 3, 4, 5, 6, 7, 8, 9].map((i) => tfun.replace(/%k%/g, i.toString()).replace(/%kdec%/g, (i - 1).toString())), tentry].join("\n");
        }
        else {
            return `
            ${decl}
            (ite (and (<= 0 ${iv}) (< ${iv} (bsq_term_list_size this)))
                (let ((result (bsq_term_list_at (bsq_term_list_entries this) ${iv})))
                    (ite (is-Result_bsq_list_h@result_with_code) (${resulttype}@result_with_code (result_bmc ${inv.sourceLocation.line})) (${resulttype}@result_success (Result_bsq_list_h@result_success result))
                )
                (${resulttype}@result_with_code (result_error ${inv.sourceLocation.pos})))
            )
            `.trim();
        }
    })

    .set("list_at", (smtgen: SMTLIBGenerator, inv: MIRInvokePrimitiveDecl, decl: string) => {
        const rcvrtype = smtgen.assembly.typeMap.get(inv.params[0].type) as MIRType;
        const rtcons = smtgen.typeToSMT2Constructor(rcvrtype);
        const iv = smtgen.varNameToSMT2Name(inv.params[1].name);
        const resulttype = "Result_" + smtgen.typeToSMT2Type(smtgen.assembly.typeMap.get(inv.resultType) as MIRType);

        if (smtgen.isTypeExact(rcvrtype)) {
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
            (ite (and (<= 0 ${iv}) (< ${iv} (${rtcons}@size this)))
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
