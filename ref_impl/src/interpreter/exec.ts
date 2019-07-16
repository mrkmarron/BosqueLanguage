//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import { Interpreter } from "../interpreter/interpreter";
import { ValueOps } from "../interpreter/value";
import { MIRAssembly } from "../compiler/mir_assembly";

import * as Commander from "commander";

Commander
    .usage("<bytecode> <function> <args ...>")
    .option("<bytecode>", "Bytecode assembly to execute")
    .option("<function>", "Function to use as entrypoint")
    .option("--assert", "Enable debug assertions");

Commander.parse(process.argv);

let masm: MIRAssembly | undefined = undefined;
try {
    masm = MIRAssembly.jparse(JSON.parse(FS.readFileSync(Commander.bytecode).toString()));
}
catch (ex) {
    process.stdout.write("Failed to load bytecode assembly\n");
}

const doassert = Commander.assert !== undefined;
const ip = new Interpreter(masm as MIRAssembly, doassert, doassert, doassert);
let res: any = undefined;
try {
    res = ValueOps.diagnosticPrintValue(ip.evaluateRootNamespaceCall("NSMain", "main", []));
}
catch (ex) {
    process.stdout.write(`fail with exception -- ${ex}\n`);
    process.exit(1);
}

process.stdout.write(res);
