//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import { execSync } from "child_process";

import chalk from "chalk";

let platpathcpp: string | undefined = undefined;
let platpathsmt: string | undefined = undefined;
let platexe: string | undefined = undefined;
if (process.platform === "win32") {
    platpathcpp = "bin/win/clang.exe";
    platpathsmt = "bin/win/z3.exe";
    platexe = "doit.exe";
}
else if (process.platform === "linux") {
    platpathcpp = "bin/linux/clang";
    platpathsmt = "bin/win/z3";
    platexe = "doit.out";
}
else {
    platpathcpp = "bin/macos/clang";
    platpathsmt = "bin/win/z3";
    platexe = "doit.out";
}

const testxml = `<?xml version="1.0" encoding="UTF-8"?>
<testsuites>
  TSLIST
</testsuites>`;

abstract class TestInfo {
    readonly name: string;
    readonly expected: string;

    constructor(name: string, expected: string) {
        this.name = name;
        this.expected = expected;
    }
}

class CompileTestInfo extends TestInfo {
    constructor(name: string, expected: string | undefined) {
        super(`${name}@compile`, expected || "");
    }
}

class ExecuteTestInfo extends TestInfo {
    readonly entrypoint: string;
    readonly args: string[];

    constructor(name: string, entry: string, expected: string, ctr: number, args: string[] | undefined) {
        super(`${name}@aot--${entry}#${ctr}`, expected);
        this.entrypoint = entry;
        this.args = args || [];
    }
}

class SymbolicCheckTestInfo extends TestInfo {
    readonly entrypoint: string;

    constructor(name: string, entry: string, error: boolean | undefined) {
        super(`${name}@symbolic_test--${entry}`, (error === true) ? "sat" : "unsat");
        this.entrypoint = entry;
    }
}

class FileTestInfo {
    readonly src: string;
    readonly compiler_tests: CompileTestInfo[];
    readonly aot_tests: ExecuteTestInfo[];
    readonly symbolic_tests: SymbolicCheckTestInfo[];

    constructor(src: string, compiler_tests: CompileTestInfo[], aot_tests: ExecuteTestInfo[], symbolic_tests: SymbolicCheckTestInfo[]) {
        this.src = src;
        this.compiler_tests = compiler_tests;
        this.aot_tests = aot_tests;
        this.symbolic_tests = symbolic_tests;
    }
}

type TestSet = {
    readonly dir: string;
    readonly xmlid: string;
    readonly tests: FileTestInfo;
};

const scratchroot = Path.normalize(Path.join(__dirname, "../scratch/"));

const cppscratch = Path.normalize(Path.join(scratchroot, "cpp/"));
const cppexe = Path.normalize(Path.join(cppscratch, platexe));

const smtscratch = Path.normalize(Path.join(scratchroot, "smt/"));

const clangpath = Path.normalize(Path.join(__dirname, "../tooling/aot/runtime", platpathcpp));
const z3path = Path.normalize(Path.join(__dirname, "../tooling/bmc/runtime", platpathsmt));

class TestRunner {
    tests: TestSet[];

    constructor() {
        this.tests = [];
    }

    loadTestSet(testdir: string) {
        const testpath = Path.normalize(Path.join(__dirname, "tests", testdir, "test.json"));
        const tdata = JSON.parse(FS.readFileSync(testpath).toString());

        for (let i = 0; i < tdata.length; ++i) {
            const testentry = tdata[i];

            const src = testentry.src;
            let compiler_tests: CompileTestInfo[] = [];
            let aot_tests: ExecuteTestInfo[] = [];
            let symbolic_tests: SymbolicCheckTestInfo[] = [];

            for (let j = 0; j < testentry.tests.length; ++j) {
                const test = testentry.tests[j];
                if (test.kind === "compile") {
                    compiler_tests.push(new CompileTestInfo(src, test.expected));
                }
                else if (test.kind === "aot") {
                    aot_tests.push(new ExecuteTestInfo(src, test.entrypoint, test.expected, aot_tests.length, test.args));
                }
                else if (test.kind === "sym") {
                    symbolic_tests.push(new SymbolicCheckTestInfo(src, test.entrypoint, test.error));
                }
                else {
                    process.stderr.write("Unknown test kind");
                    process.exit(1);
                }
            }

            this.tests.push({ dir: testdir, xmlid: `${testdir}_testdir`, tests: new FileTestInfo(src, compiler_tests, aot_tests, symbolic_tests) });
        }
    }

    private runCompileTest(testsrc: string, test: CompileTestInfo): string {
        const runnerapp = Path.join(__dirname, "runner.js");
        try {
            return execSync(`node ${runnerapp} -t ${testsrc}`).toString().trim();
        }
        catch (ex) {
            return ex.message + "\n" + ex.output[1].toString() + "\n" + ex.output[2].toString();
        }
    }

    private runAOTTest(testsrc: string, test: ExecuteTestInfo): string {
        const runnerapp = Path.join(__dirname, "runner.js");
        try {
            execSync(`node ${runnerapp} -c "NSTest::${test.entrypoint}" ${testsrc}`);

            process.chdir(cppscratch);
            execSync(`${clangpath} -Wall -g -DBDEBUG -o ${cppexe} *.cpp`);
            const res = execSync(`${cppexe} ${test.args.join(" ")}`);
            return res.toString().trim();
        }
        catch (ex) {
            return ex.message + "\n" + ex.output[1].toString() + "\n" + ex.output[2].toString();
        }
    }

    private runSymbolicTest(testsrc: string, test: SymbolicCheckTestInfo): string {
        const runnerapp = Path.join(__dirname, "runner.js");
        try {
            execSync(`node ${runnerapp} -v "NSTest::${test.entrypoint}" ${testsrc}`);
        
            process.chdir(smtscratch);
            const res = execSync(`${z3path} -smt2 scratch.smt2`);
            return res.toString().trim();
        }
        catch (ex) {
            return ex.message + "\n" + ex.output[1].toString() + "\n" + ex.output[2].toString();
        }
    }

    private runTestSet(ts: TestSet, id: number): { total: number, failed: number, results: string } {
        const totaltests = ts.tests.compiler_tests.length + ts.tests.aot_tests.length + ts.tests.symbolic_tests.length;

        process.stdout.write("--------\n");
        process.stdout.write(`Running ${chalk.bold(ts.dir)} suite with ${chalk.bold(totaltests.toString())} tests...\n`);

        const tsstring = new Date().toISOString().slice(0, -5);
        const start = Date.now();

        let tresults: string[] = [];
        let fail = 0;

        for(let i = 0; i < ts.tests.compiler_tests.length; ++i) {
            const ctest = ts.tests.compiler_tests[i];
            const testsrc = Path.normalize(Path.join(__dirname, "tests", ts.dir, ts.tests.src));

            process.stdout.write(`Running ${ctest.name}...`);
            const tstart = Date.now();

            const cr = this.runCompileTest(testsrc, ctest);
            if (ctest.expected === cr) {
                process.stdout.write(chalk.green("pass\n"));
                tresults.push(`<testcase name="${ctest.name}" class="" time="${(Date.now() - tstart) / 1000}"/>`);

            }
            else {
                fail++;
                const failmsg = `fail with ${cr} expected ${ctest.expected}`;
                tresults.push(`<testcase name="${ctest.name}" class="" time="${(Date.now() - tstart) / 1000}"><failure message="${failmsg}"/></testcase>`);

                process.stdout.write(chalk.red(`${failmsg}\n`));
            }
        }

        for(let i = 0; i < ts.tests.aot_tests.length; ++i) {
            const ctest = ts.tests.aot_tests[i];
            const testsrc = Path.normalize(Path.join(__dirname, "tests", ts.dir, ts.tests.src));

            process.stdout.write(`Running ${ctest.name}...`);
            const tstart = Date.now();

            const cr = this.runAOTTest(testsrc, ctest);
            if (ctest.expected === cr) {
                process.stdout.write(chalk.green("pass\n"));
                tresults.push(`<testcase name="${ctest.name}" class="" time="${(Date.now() - tstart) / 1000}"/>`);

            }
            else {
                fail++;
                const failmsg = `fail with ${cr} expected ${ctest.expected}`;
                tresults.push(`<testcase name="${ctest.name}" class="" time="${(Date.now() - tstart) / 1000}"><failure message="${failmsg}"/></testcase>`);

                process.stdout.write(chalk.red(`${failmsg}\n`));
            }
        }

        for(let i = 0; i < ts.tests.symbolic_tests.length; ++i) {
            const vtest = ts.tests.symbolic_tests[i];
            const testsrc = Path.normalize(Path.join(__dirname, "tests", ts.dir, ts.tests.src));

            process.stdout.write(`Running ${vtest.name}...`);
            const tstart = Date.now();

            const cr = this.runSymbolicTest(testsrc, vtest);
            if (vtest.expected === cr) {
                process.stdout.write(chalk.green("pass\n"));
                tresults.push(`<testcase name="${vtest.name}" class="" time="${(Date.now() - tstart) / 1000}"/>`);

            }
            else {
                fail++;
                const failmsg = `fail with ${cr} expected ${vtest.expected}`;
                tresults.push(`<testcase name="${vtest.name}" class="" time="${(Date.now() - tstart) / 1000}"><failure message="${failmsg}"/></testcase>`);

                process.stdout.write(chalk.red(`${failmsg}\n`));
            }
        }

        const tsres = `<testsuite name="${ts.xmlid}" tests="${totaltests}" errors="0" failures="${fail}" id="${id}" time="${(Date.now() - start) / 1000}" timestamp="${tsstring}" hostname="localhost" package="${ts.xmlid}"><properties></properties><system-out/><system-err/>${tresults.join("\n")}</testsuite>`;
        if (fail === 0) {
            process.stdout.write(chalk.green("Completed successfully.\n\n"));
        }
        else {
            process.stdout.write(chalk.red(`Completed with ${chalk.bold(fail.toString())} failures.\n\n`));
        }

        return {
            total: totaltests,
            failed: fail,
            results: tsres
        }
    }

    run() {
        let fail = 0;

        let tr = [];
        for (let i = 0; i < this.tests.length; ++i) {
            const results = this.runTestSet(this.tests[i], i);
            if (results.failed !== 0) {
                fail++;
            }

            tr.push(results.results);
        }

        FS.writeFileSync("TEST-RESULTS.xml", testxml.replace("TSLIST", tr.join("\n")));

        if (fail === 0) {
            process.stdout.write(chalk.green(chalk.bold(`\nAll ${this.tests.length} test suites passed!\n`)));
        }
        else {
            process.stdout.write(chalk.red(chalk.bold(`\n${fail} test suites had failures...\n`)));
        }
    }
}

function runAll() {
    const runner = new TestRunner();

    runner.loadTestSet("expression");

    runner.run();
}

////
//Entrypoint

setImmediate(() => runAll());
