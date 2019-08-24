import { MIRInvokePrimitiveDecl, MIRType } from "../../compiler/mir_assembly";
import { SMTLIBGenerator, SMTValue } from "./generator";

//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

type BuiltinTypeEmit = (ttstring: string, tcstring: string, cstring: string) => string;
type BuiltinCallEmit = (smtgen: SMTLIBGenerator, inv: MIRInvokePrimitiveDecl, decl: string) => string;

const BuiltinCalls = new Map<string, BuiltinCallEmit>()
    .set("list_createofsize", (smtgen: SMTLIBGenerator, inv: MIRInvokePrimitiveDecl, decl: string) => {
        return "";
    })
    .set("list_empty", (smtgen: SMTLIBGenerator, inv: MIRInvokePrimitiveDecl, decl: string) => {
        const rcvrtype = smtgen.assembly.typeMap.get(inv.params[0].type) as MIRType;
        const rtcons = smtgen.typeToSMT2Constructor(rcvrtype);
        const resulttype = "Result_" + smtgen.typeToSMT2Type(smtgen.assembly.typeMap.get(inv.resultType) as MIRType);

        return `(${resulttype}@result_success (= (${rtcons}@size this) 0))`;
    })
    .set("list_size", (smtgen: SMTLIBGenerator, inv: MIRInvokePrimitiveDecl, decl: string) => {
        const rcvrtype = smtgen.assembly.typeMap.get(inv.params[0].type) as MIRType;
        const rtcons = smtgen.typeToSMT2Constructor(rcvrtype);
        const resulttype = "Result_" + smtgen.typeToSMT2Type(smtgen.assembly.typeMap.get(inv.resultType) as MIRType);

        return `(${resulttype}@result_success (${rtcons}@size this))`;
    })

    .set("list_filter", (smtgen: SMTLIBGenerator, inv: MIRInvokePrimitiveDecl, decl: string) => {
        return "";
    })

    .set("list_at", (smtgen: SMTLIBGenerator, inv: MIRInvokePrimitiveDecl, decl: string) => {
        const rcvrtype = smtgen.assembly.typeMap.get(inv.params[0].type) as MIRType;
        const rtcons = smtgen.typeToSMT2Constructor(rcvrtype);
        const iv = smtgen.varNameToSMT2Name(inv.params[1].name);
        const resulttype = "Result_" + smtgen.typeToSMT2Type(smtgen.assembly.typeMap.get(inv.resultType) as MIRType);

        const restype = smtgen.assembly.typeMap.get(inv.resultType) as MIRType;
        const accessexp = smtgen.coerceUnBoxIfNeeded(new SMTValue(`(select (${rtcons}@contents this) ${iv})`), smtgen.anyType, restype);

        return `
        ${decl}
        (ite (and (<= 0 ${iv}) (< ${iv} (${rtcons}@size this)))
            (${resulttype}@result_success ${accessexp.emit()})
            (${resulttype}@result_with_code (result_error ${inv.sourceLocation.pos})))
        )
        `;
    });

const BuiltinTypes = new Map<string, BuiltinTypeEmit>()
    .set("List", (ttstring: string, tcstring: string, cstring: string) => {
        return `(${tcstring}@nil (${tcstring}@cons (${tcstring}@size Int) (${tcstring}@h ${cstring}) (${tcstring}@t ${ttstring})))`;
});

export { BuiltinTypeEmit, BuiltinTypes, BuiltinCallEmit, BuiltinCalls };
