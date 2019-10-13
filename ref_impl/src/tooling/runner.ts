//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

//
//THIS IS A TEMPORARY RUNNER FILE FOR THE SMT AND COMPILER WHILE WE BOOTSTRAP -- DELETE LATER
//

import * as FS from "fs";
import * as Path from "path";

import * as Commander from "commander";
import { MIRAssembly, PackageConfig, MIRInvokeDecl } from "../compiler/mir_assembly";
import { MIREmitter } from "../compiler/mir_emitter";
import { SMTBodyEmitter } from "./bmc/smtbody_emitter";
import { SMTTypeEmitter } from "./bmc/smttype_emitter";
import { CPPBodyEmitter } from "./aot/cppbody_emitter";
import { CPPTypeEmitter } from "./aot/cpptype_emitter";

function generateMASM(files: string[], corelibpath: string): MIRAssembly {
    process.stdout.write("Reading code...\n");

    let bosque_dir: string = Path.normalize(Path.join(__dirname, "../../"));

    let code: { relativePath: string, contents: string }[] = [];
    try {
        const coredir = Path.join(bosque_dir, corelibpath, "/core.bsq");
        const coredata = FS.readFileSync(coredir).toString();

        const collectionsdir = Path.join(bosque_dir, corelibpath, "/collections.bsq");
        const collectionsdata = FS.readFileSync(collectionsdir).toString();

        code = [{ relativePath: coredir, contents: coredata }, { relativePath: collectionsdir, contents: collectionsdata }];
        for (let i = 0; i < files.length; ++i) {
            const file = { relativePath: files[i], contents: FS.readFileSync(files[i]).toString() };
            code.push(file);
        }
    }
    catch (ex) {
        process.stdout.write(`Read failed with exception -- ${ex}\n`);
        process.exit(1);
    }

    process.stdout.write("Compiling assembly...\n");

    const { masm, errors } = MIREmitter.generateMASM(new PackageConfig(), true, true, true, code);
    if (errors.length !== 0) {
        for (let i = 0; i < errors.length; ++i) {
            process.stdout.write(`Parse error -- ${errors[i]}\n`);
        }

        process.exit(1);
    }

    return masm as MIRAssembly;
}

function smtlibGenerate(masm: MIRAssembly, idecl: MIRInvokeDecl): string {
    const smtgen = new SMTBodyEmitter(masm, new SMTTypeEmitter(masm));
    const smtcode = smtgen.generateInvoke(idecl);

    return smtcode[1];
}

function cppGenerate(masm: MIRAssembly, idecl: MIRInvokeDecl): string {
    const cppgen = new CPPBodyEmitter(masm, new CPPTypeEmitter(masm));
    const cppcode = cppgen.generateInvoke(idecl);

    return cppcode[1];
}

Commander
    .option("-v --verify <entrypoint>", "Check for errors reachable from specified entrypoint")
    .option("-c --compile <entrypoint>", "Compile the specified entrypoint");

Commander.parse(process.argv);

if (Commander.args.length === 0) {
    process.stdout.write("Error -- Please specify at least one source file as an argument");
    process.exit(1);
}

const massembly = generateMASM(Commander.args, Commander.verify ? "src/core/verify/" : "src/core/compile/");
const entrypoint = massembly.invokeDecls.get(Commander.verify || Commander.compile) as MIRInvokeDecl;

if (Commander.verify !== undefined) {
    setImmediate(() => process.stdout.write(smtlibGenerate(massembly, entrypoint) + "\n"));
}
else {
    setImmediate(() => process.stdout.write(cppGenerate(massembly, entrypoint) + "\n"));
}
