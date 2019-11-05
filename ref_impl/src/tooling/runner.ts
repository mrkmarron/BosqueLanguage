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
import { MIRAssembly, PackageConfig, MIRInvokeBodyDecl } from "../compiler/mir_assembly";
import { MIREmitter } from "../compiler/mir_emitter";
import { CPPEmitter } from "./aot/cppdecls_emitter";
import { SMTEmitter } from "./bmc/smtdecls_emitter";
import { sanitizeStringForCpp } from "./aot/cpputils";

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

Commander
    .option("-v --verify <entrypoint>", "Check for errors reachable from specified entrypoint")
    .option("-c --compile <entrypoint>", "Compile the specified entrypoint");

Commander.parse(process.argv);

if (Commander.args.length === 0) {
    process.stdout.write("Error -- Please specify at least one source file as an argument");
    process.exit(1);
}

const massembly = generateMASM(Commander.args, Commander.verify ? "src/core/direct/" : "src/core/direct/");

if (Commander.verify !== undefined) {
    setImmediate(() => {
        const smt_runtime = Path.join(__dirname, "bmc/runtime/smtruntime.smt2");

        const sparams = SMTEmitter.emit(massembly);
        const lsrc = FS.readFileSync(smt_runtime).toString();
        const gensrc = lsrc
            .replace(";;FIXED_TUPLE_DECLS_FWD;;", "  " + sparams.fixedtupledecls_fwd)
            .replace(";;FIXED_RECORD_DECLS_FWD;;", "  " + sparams.fixedrecorddecls_fwd)
            .replace(";;FIXED_TUPLE_DECLS;;", "  " + sparams.fixedtupledecls)
            .replace(";;FIXED_RECORD_DECLS;;", "  " + sparams.fixedrecorddecls)
            .replace(";;NOMINAL_DECLS_FWD;;", "  " + sparams.typedecls_fwd)
            .replace(";;NOMINAL_DECLS;;", "  " + sparams.typedecls)
            .replace(";;NOMINAL_RESULT_FWD;;", "  " + sparams.resultdecls_fwd)
            .replace(";;NOMINAL_RESULT;;", "  " + sparams.resultdecls)
            .replace(";;FUNCTION_DECLS;;", "  " + sparams.function_decls);

        const entrypoint = massembly.invokeDecls.get(Commander.verify) as MIRInvokeBodyDecl;
        let contents = gensrc;
        if (entrypoint.params.length !== 0) {
            process.stderr.write("Entrypoint args are not currently supported!!!\n");
            process.exit(1);
        }

        const chkinfo = SMTEmitter.emitEntrypointCall(massembly, entrypoint);
        contents = contents
            .replace(";;ARG_VALUES;;", chkinfo.arginfo)
            .replace(";;INVOKE_ACTION;;", chkinfo.callinfo)
            .replace(";;GET_MODEL;;", "(get-model)");

        const outfile = Path.join("c:\\Users\\marron\\Desktop\\smt_scratch\\", "scratch.smt2");
        FS.writeFileSync(outfile, contents);
    });
}
else {
    setImmediate(() => {
        const cpp_runtime = Path.join(__dirname, "aot/runtime/");

        const cparams = CPPEmitter.emit(massembly);
        const lsrc = FS.readdirSync(cpp_runtime);
        const linked = lsrc.map((fname) => {
            const contents = FS.readFileSync(Path.join(cpp_runtime, fname)).toString();
            const bcontents = contents
                .replace("//%%NOMINAL_TYPE_ENUM_DECLARE", "    " + cparams.nominalenums)
                .replace("//%%STATIC_STRING_DECLARE%%", "  " + cparams.conststring_declare)
                .replace("//%%STATIC_STRING_CREATE%%", "  " + cparams.conststring_create)
                .replace("//%%FIXED_RECORD_PROPERTY_LIST_ENUM_DECLARE", "    " + cparams.fixedrecord_property_lists)
                .replace("//%%PROPERTY_ENUM_DECLARE", "    " + cparams.propertyenums)
                .replace("//%%PROPERTY_NAMES", "  " + cparams.propertynames)
                .replace("//%%VFIELD_DECLS", "    " + cparams.vfield_decls)
                .replace("//%%VMETHOD_DECLS", "  " + cparams.propertynames);

            return { file: fname, contents: bcontents };
        });

        const maincpp = "#include \"bsqruntime.h\"\n"
            + "namespace BSQ\n"
            + "{\n/*forward type decls*/\n"
            + cparams.typedecls_fwd
            + "\n\n/*forward function decls*/\n"
            + cparams.funcdecls_fwd
            + "\n\n/*type decls*/\n"
            + cparams.typedecls
            + "\n\n/*function decls*/\n"
            + cparams.funcdecls
            + "}\n\n"
            + "\n\n/*main decl*/\n"
            + `int main(int argc, char* argv) { try { return BSQ::${sanitizeStringForCpp(Commander.compile)}(); } catch (BSQ::BSQAbort& abrt) HANDLE_BSQ_ABORT(abrt) }\n`;
        linked.push({ file: "main.cpp", contents: maincpp });

        linked.forEach((fp) => {
            const outfile = Path.join("c:\\Users\\marron\\Desktop\\cpp_scratch\\", fp.file);
            FS.writeFileSync(outfile, fp.contents);
        });
    });
}
