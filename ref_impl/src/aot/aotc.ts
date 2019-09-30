//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";

import { MIREmitter } from "../compiler/mir_emitter";
import { PackageConfig, MIRAssembly, MIRInvokeBodyDecl, MIRType } from "../compiler/mir_assembly";

import chalk from "chalk";
import * as Commander from "commander";
import { AOTTypeGenerator } from "./aot_type_generator";
import { AOTCodeGenerator } from "./aot_op_generator";
import { sanitizeForCpp } from "./utils";

/*
let cpp_cmd: string | undefined = undefined;
if (process.platform === "win32") {
    cpp_cmd = "msvc";
}
else if (process.platform === "linux") {
    cpp_cmd = undefined;
}
else {
    cpp_cmd = undefined;
}
*/

const runtimedir = Path.join(__dirname, "../../src/aot/runtime");

function generateMASM(files: string[]): MIRAssembly {
    process.stdout.write("Reading code...\n");

    let bosque_dir: string = Path.normalize(Path.join(__dirname, "../../"));

    let code: { relativePath: string, contents: string }[] = [];
    try {
        const coredir = Path.join(bosque_dir, "src/core/core.bsq");
        const coredata = FS.readFileSync(coredir).toString();

        const collectionsdir = Path.join(bosque_dir, "src/core/collections.bsq");
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

function generateCPP(masm: MIRAssembly, outdir: string) {
    const typegen = new AOTTypeGenerator(masm);
    const cppgen = new AOTCodeGenerator(masm, typegen);

    try {
        process.stdout.write("Generating C++ Code...\n");

        const cppcode = cppgen.generateAssembly();

        process.stdout.write("Writing...\n");
        FS.writeFileSync(Path.join(outdir, "assembly.h"), cppcode);

        if (masm.entryPoints.length !== 1) {
            process.stdout.write(chalk.red(`must have unique entrypoint\n`));
            process.exit(1);
        }

        const mainname = masm.entryPoints[0];
        const mainf = masm.invokeDecls.get(mainname) as MIRInvokeBodyDecl;
        const coerce = cppgen.coerceBoxIfNeeded(`${sanitizeForCpp(mainname)}()`, masm.typeMap.get(mainf.resultType) as MIRType, cppgen.typegen.anyType);
        FS.writeFileSync(Path.join(outdir, "main.cpp"), `#include "assembly.h"\nint main() { printf("%s\\n", BSQ::displayformat(${coerce}).c_str()); fflush(stdout); return 0; }`);

        process.stdout.write("Copying runtime...\n");
        FS.readdirSync(runtimedir)
        .filter((file) => file.endsWith(".h") || file.endsWith(".cpp"))
        .forEach((file) => FS.copyFileSync(Path.join(runtimedir, file), Path.join(outdir, file)));

        process.stdout.write("Done\n");
    }
    catch (ex) {
        process.stdout.write(chalk.red(`fail with exception -- ${ex}\n`));
        process.exit(1);
    }
}

Commander
    .option("-c --compile <out.exe>", "Compile the code and generate an executable that calls the single entrypoint")
    .option("-g --generate <outdir>", "Generate the C++ code for the Bosque program");

Commander.parse(process.argv);

if (Commander.args.length === 0) {
    process.stdout.write("Error -- Please specify at least one source file as an argument");
    process.exit(1);
}

const massembly = generateMASM(Commander.args);

if (Commander.generate !== undefined) {
    setImmediate(() => generateCPP(massembly, Commander.generate));
}
if (Commander.compile !== undefined) {
    process.stdout.write("Not Implemented!!!\n");
}
