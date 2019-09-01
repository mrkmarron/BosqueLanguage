//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import { execSync } from "child_process";

import { MIREmitter } from "../compiler/mir_emitter";
import { PackageConfig, MIRAssembly, MIRInvokeBodyDecl, MIRType } from "../compiler/mir_assembly";
import { SMTLIBGenerator } from "./smtlib/generator";

import chalk from "chalk";
import * as Commander from "commander";

let z3path: string | undefined = undefined;
if (process.platform === "win32") {
    z3path = Path.resolve("./utils/win/z3/z3.exe");
}
else if (process.platform === "linux") {
    z3path = Path.resolve("./utils/linux/z3/z3.exe");
}
else {
    z3path = Path.resolve("./utils/macos/z3/z3.exe");
}

function smtlib2Generate(files: string[]): { smtcode: string, smtgen: SMTLIBGenerator } {
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

    process.stdout.write(`Generating SMTLIB...\n`);

    const smtgen = new SMTLIBGenerator(masm as MIRAssembly);
    const smtcode = smtgen.generateSMTAssembly();

    return { smtcode: smtcode, smtgen: smtgen };
}

function smtlib2Compile(files: string[], trgt: string) {
    try {
        const smtlib = smtlib2Generate(files);

        process.stdout.write("Writing SMTLIB...\n");
        FS.writeFileSync(trgt, smtlib.smtcode);
    }
    catch (ex) {
        process.stdout.write(`Fail with exception -- ${ex}\n`);
        process.exit(1);
    }

    process.stdout.write(`Success, smtlib output in ${trgt}\n`);
    process.exit(0);
}

function checkSingleEntryPointSMT(files: string[], entrypoint: string, icheck: boolean, rparallel: boolean): string {
    const { smtgen, smtcode } = smtlib2Generate(files);

    const ep = [...smtgen.assembly.invokeDecls.values()].find((idcl) => idcl.key === entrypoint)
    if (ep === undefined) {
        process.stdout.write(`Entrypoint function ${entrypoint} is not defined -- exiting\n`);
        process.exit(1);
    }
    const ivk = ep as MIRInvokeBodyDecl;
    const restype = smtgen.typeToSMT2Type(smtgen.assembly.typeMap.get(ivk.resultType) as MIRType);

    const argsdecls = ivk.params.map((fp) => `(declare-const ${fp.name} ${smtgen.typeToSMT2Type(smtgen.assembly.typeMap.get(fp.type) as MIRType)})`);
    const resdecl = `(declare-const res Result_${restype})`;
    const call = ivk.params.length !== 0 ? `(${smtgen.invokenameToSMT2(ivk.key)} ${ivk.params.map((fp) => fp.name).join(" ")})` : smtgen.invokenameToSMT2(ivk.key);
    const cassert = `(assert (= res ${call}))`;

    const excludeerrors = [...smtgen.errormap].filter((err) => err[1][0] === ivk.srcFile && err[1][1].line === ivk.sourceLocation.line).map((err) => err[0]);
    const errorasrt = excludeerrors.length === 1
        ? `(assert (and
            (is-Result_${restype}@result_with_code res)
            (is-result_error (Result_${restype}@result_code_value res))
            (not (= ${excludeerrors[0]} (error_id (Result_${restype}@result_code_value res))))
           ))`
        : `(assert (and
            (is-Result_${restype}@result_with_code res)
            (is-result_error (Result_${restype}@result_code_value res))
           ))`;

    const smtcall = smtcode
        + "\n\n"
        + argsdecls.join("\n")
        + "\n\n"
        + resdecl
        + "\n\n"
        + cassert + "\n" + errorasrt
        + "\n\n"
        + "(check-sat)\n";

    if (!icheck) {
        const res = execSync(`${z3path} -smt2 -in `, { input: smtcall });
        return res.toString().trim();
    }
    else {
        return "NOT IMPLEMENTED YET!!!";
    }
}

function bmcRunAny(files: string[], entrypoint: string | undefined) {
    try {
        if (entrypoint) {
            const result = checkSingleEntryPointSMT(files, entrypoint, false, false);
            if (result === "unsat") {
                process.stdout.write(chalk.green("No errors found\n"));
            }
            else {
                process.stdout.write(chalk.red("Errors detected!!!\n"));
                process.stdout.write("Run with -individual for more information\n");
            }
        }
        else {
            process.stdout.write("NOT IMPLEMENTED YET\n");
            process.exit(1);
        }
    }
    catch (ex) {
        process.stdout.write(`Failed with exception -- ${ex}\n`);
        process.exit(1);
    }
}

function bmcRunEach(files: string[], entrypoint: string | undefined) {
    process.stdout.write("NOT IMPLEMENTED YET\n");
    process.exit(1);
}

Commander
.option("-c --check [entrypoint]", "Check for errors reachable from specified entrypoint")
.option("-e --error <line>", "Only check for error associated with the given line" )
.option("-i --individual", "Check for errors individually")
.option("-g --generate [file]", "Generate the smt2lib output for the assembly");

Commander.parse(process.argv);

if (Commander.args.length === 0) {
    process.stdout.write("Error -- Please specify at least one source file as an argument");
    process.exit(1);
}

if (Commander.generate !== undefined) {
    setImmediate(() => smtlib2Compile(Commander.args, Commander.output || "a.smt2"));
}
else {
    if (Commander.individual) {
        setImmediate(() => bmcRunEach(Commander.args, Commander.check));
    }
    else {
        setImmediate(() => bmcRunAny(Commander.args, Commander.check));
    }
}
