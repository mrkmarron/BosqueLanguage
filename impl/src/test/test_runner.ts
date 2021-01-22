//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";
import * as FS from "fs";
import * as Path from "path";

import chalk from "chalk";

const testroot = Path.normalize(Path.join(__dirname, "tests"));

abstract class IndividualTestInfo {
    readonly name: string;
    readonly fullname: string;

    readonly code: string;

    readonly extraSrc: string | undefined;

    constructor(name: string, fullname: string, code: string, extraSrc: string | undefined) {
        this.name = name;
        this.fullname = fullname;
        this.code = code;
        this.extraSrc = extraSrc;
    }

    generateTestPlan(restriction: string, tests: IndividualTestInfo[]) {
        if(restriction === "*" || this.fullname.startsWith(restriction)) {
            tests.push(this);
        }
    }
}

class IndividualRefuteTestInfo extends IndividualTestInfo {
    readonly line: number;

    private static ctemplate = 
"namespace NSMain;\
\
%%SIG%% {\
    assert %%ACTION%%;\
    return true;\
}\
\
%%CODE%%\
";

    constructor(name: string, fullname: string, code: string, line: number, extraSrc: string | undefined) {
        super(name, fullname, code, extraSrc);

        this.line = line;
    }

    static create(name: string, fullname: string, sig: string, action: string, code: string, extraSrc: string | undefined): IndividualRefuteTestInfo {
        const rcode = IndividualRefuteTestInfo.ctemplate
            .replace("%%SIG%%", sig)
            .replace("%%ACTION%%", action)
            .replace("%%CODE%%", code);

        return new IndividualRefuteTestInfo(name, fullname, rcode, 4, extraSrc);
    }
}

class IndividualReachableTestInfo extends IndividualTestInfo {
    readonly line: number;

    private static ctemplate = 
"namespace NSMain;\
\
%%SIG%% {\
    assert !(%%ACTION%%);\
    return true;\
}\
\
%%CODE%%\
";

    constructor(name: string, fullname: string, code: string, line: number, extraSrc: string | undefined) {
        super(name, fullname, code, extraSrc);

        this.line = line;
    }

    static create(name: string, fullname: string, sig: string, action: string, code: string, extraSrc: string | undefined): IndividualReachableTestInfo {
        const rcode = IndividualReachableTestInfo.ctemplate
            .replace("%%SIG%%", sig)
            .replace("%%ACTION%%", action)
            .replace("%%CODE%%", code);

        return new IndividualReachableTestInfo(name, fullname, rcode, 4, extraSrc);
    }
}

type APITestGroupJSON = {
    test: string,
    src: string | null,
    sig: string,
    code: string,
    refutes: string[],
    reachables: string[]
};

class APITestGroup {
    readonly groupname: string;
    readonly tests: IndividualTestInfo[];

    constructor(groupname: string, tests: IndividualTestInfo[]) {
        this.groupname = groupname;
        this.tests = tests;
    }

    static create(scopename: string, spec: APITestGroupJSON): APITestGroup {
        const groupname = `${scopename}.${spec.test}`;
        const refutes = spec.refutes.map((tt, i) => IndividualRefuteTestInfo.create(`${i}`, `${groupname}.refute#${i}`, spec.sig, tt, spec.code, spec.src || undefined));
        const reachables = spec.reachables.map((tt, i) => IndividualReachableTestInfo.create(`${i}`, `${groupname}.reach#${i}`, spec.sig, tt, spec.code, spec.src || undefined));

        return new APITestGroup(groupname, [...refutes, ...reachables]);
    }

    generateTestPlan(restriction: string, tests: IndividualTestInfo[]) {
        this.tests.forEach((tt) => tt.generateTestPlan(restriction, tests));
    }
}

type CategoryTestGroupJSON = {
    suite: string,
    tests: APITestGroupJSON[]
};

class CategoryTestGroup {
    readonly categoryname: string;
    readonly apitests: APITestGroup[];

    constructor(categoryname: string, apitests: APITestGroup[]) {
        this.categoryname = categoryname;
        this.apitests = apitests;
    }

    static create(scopename: string, spec: CategoryTestGroupJSON) {
        const categoryname = `${scopename}.${spec.suite}`;
        const apitests = spec.tests.map((tt) => APITestGroup.create(categoryname, tt));

        return new CategoryTestGroup(categoryname, apitests);
    }

    generateTestPlan(restriction: string, tests: IndividualTestInfo[]) {
        this.apitests.forEach((tt) => tt.generateTestPlan(restriction, tests));
    }
}

class TestFolder {
    readonly path: string;
    readonly testname: string;

    readonly tests: CategoryTestGroup[];

    constructor(path: string, testname: string, tests: CategoryTestGroup[]) {
        this.path = path;
        this.testname = testname;
        this.tests = tests;
    }

    generateTestPlan(restriction: string, tests: IndividualTestInfo[]) {
        this.tests.forEach((tt) => tt.generateTestPlan(restriction, tests));
    }
}

class TestSuite {
    readonly tests: TestFolder[];

    constructor(tests: TestFolder[]) {
        this.tests = tests;
    }

    generateTestPlan(restriction: string): TestPlan {
        let tests: IndividualTestInfo[] = [];
        this.tests.forEach((tt) => tt.generateTestPlan(restriction, tests));

        return new TestPlan(this, tests);
    }
}

class TestPlan {
    readonly suite: TestSuite;
    readonly tests: IndividualTestInfo[];

    constructor(suite: TestSuite, tests: IndividualTestInfo[]) {
        this.suite = suite;
        this.tests = tests;
    }
}

class TestRunResults {
    readonly suite: TestSuite;

    passed: Map<string, IndividualTestInfo> = new Map<string, IndividualTestInfo>();
    failed: Map<string, IndividualTestInfo> = new Map<string, IndividualTestInfo>();
    errors: Map<string, IndividualTestInfo> = new Map<string, IndividualTestInfo>();

    constructor(suite: TestSuite) {
        this.suite = suite;
    }

    getOverallResults(): {total: number, passed: number, failed: number, errors: number} {
        return {
            total: this.suite.tests.length,
            passed: this.passed.size,
            failed: this.failed.size,
            errors: this.errors.size
        }
    }
}

function loadTestSuite(): TestSuite {
    const tdirs = FS.readdirSync(testroot);

    let tfa: TestFolder[] = [];
    for(let i = 0; i < tdirs.length; ++i) {
        const dpath = Path.join(testroot, tdirs[i]);
        const tfiles = FS.readdirSync(dpath).filter((fp) => fp.endsWith(".json"));

        let ctgs: CategoryTestGroup[] = [];
        for (let j = 0; j < tfiles.length; ++j) {
            const fcontents = JSON.parse(FS.readFileSync(tfiles[j], "utf8")) as CategoryTestGroupJSON;
            ctgs.push(CategoryTestGroup.create(`${tdirs[i]}.${Path.basename(tfiles[j])}`, fcontents));
        }

        tfa.push(new TestFolder(dpath, tdirs[i], ctgs));
    }

    return new TestSuite(tfa);
}

class TestRunner {
    readonly suite: TestSuite;
    readonly plan: TestPlan;

    pending: IndividualTestInfo[];
    queued: string[];
    results: TestRunResults;

    private testCompleteAction(test: IndividualTestInfo, result: "pass" | "fail" | "unknown/timeout" | "error", info?: string) {
        const qidx = this.queued.findIndex((vv) => vv === test.fullname);
        assert(qidx !== -1);

        this.queued.splice(qidx, 1);

        if (result === "pass") {
            this.results.passed.set(test.fullname, test);
        }
        else if (result === "fail") {
            xxxx;
        }
        else {
            xxxx;
        }
    }

    private generateTestResultCallback(test: IndividualTestInfo) {
        return (result: "pass" | "fail" | "unknown/timeout" | "error", info?: string) => {
            this.testCompleteAction(test, result, info);
        };
    }

    private checkAndEnqueueTests() {
        xxxx;
    }

    constructor(suite: TestSuite, plan: TestPlan) {
        this.suite = suite;
        this.plan = plan;

        this.pending = [...this.plan.tests];
        this.queued = [];
        this.results = new TestRunResults(suite);
    }

    xxxx;

    loadTestSet(testdir: string) {
        const testpath = Path.normalize(Path.join(__dirname, "tests", testdir, "test.json"));
        const tdata = JSON.parse(FS.readFileSync(testpath).toString());

        for (let i = 0; i < tdata.length; ++i) {
            const testentry = tdata[i];

            const src = testentry.src;
            let compiler_tests: CompileTestInfo[] = [];
            let aot_tests: ExecuteTestInfo[] = [];
            let symbolic_tests: SymbolicCheckTestInfo[] = [];
            let symbolic_execs: SymbolicExecTestInfo[] = [];

            for (let j = 0; j < testentry.tests.length; ++j) {
                const test = testentry.tests[j];
                if (test.kind === "compile") {
                    compiler_tests.push(new CompileTestInfo(src, test.expected));
                }
                else if (test.kind === "aot") {
                    aot_tests.push(new ExecuteTestInfo(src, test.entrypoint, test.expected, aot_tests.length, test.args));
                }
                else if (test.kind === "symtest") {
                    symbolic_tests.push(new SymbolicCheckTestInfo(src, test.entrypoint, test.error));
                }
                else if (test.kind === "symexec") {
                    symbolic_execs.push(new SymbolicExecTestInfo(src, test.entrypoint, test.expected));
                }
                else {
                    process.stderr.write("Unknown test kind");
                    process.exit(1);
                }
            }

            const srcpath = Path.join(testdir, src);
            this.tests.push({ src: srcpath, xmlid: `${srcpath.replace(/(\\)|(\/)/g, "_")}_tests`, tests: new FileTestInfo(src, compiler_tests, aot_tests, symbolic_tests, symbolic_execs) });
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
            execSync(`${clangpath} -std=c++17 -g -DBDEBUG -o ${cppexe} *.cpp`);
            const res = execSync(`${cppexe} ${test.args.join(" ")}`).toString().trim();
            return res;
        }
        catch (ex) {
            return ex.message + "\n" + ex.output[1].toString() + "\n" + ex.output[2].toString();
        }
    }

    private runSymbolicCheckTest(testsrc: string, test: SymbolicCheckTestInfo): string {
        const runnerapp = Path.join(__dirname, "runner.js");
        try {
            execSync(`node ${runnerapp} -s "NSTest::${test.entrypoint}" ${testsrc}`);
        
            process.chdir(smtscratch);
            const res = execSync(`${z3path} -smt2 scratch.smt2`).toString().trim();
            return res;
        }
        catch (ex) {
            return ex.message + "\n" + ex.output[1].toString() + "\n" + ex.output[2].toString();
        }
    }

    private runSymbolicExecTest(testsrc: string, test: SymbolicCheckTestInfo): string {
        const runnerapp = Path.join(__dirname, "runner.js");
        try {
            execSync(`node ${runnerapp} -r "NSTest::${test.entrypoint}" ${testsrc}`);

            process.chdir(smtscratch);
            const res = execSync(`${z3path} -smt2 scratch.smt2`).toString().trim();

            const splits = res.split("\n");
            const ridx = splits.findIndex((str) => str.trim().startsWith(`(define-fun @smtres@`));
            if (ridx === -1) {
                return "NO_MODEL";
            }
            else {
                const mres = splits[ridx + 1].trim();
                return mres.substring(mres.indexOf(" "), mres.length - 2).trim();
            }
        }
        catch (ex) {
            return ex.message + "\n" + ex.output[1].toString() + "\n" + ex.output[2].toString();
        }
    }

    private runTestSet(ts: TestSet, id: number): { total: number, failed: number, results: string } {
        const totaltests = ts.tests.compiler_tests.length + ts.tests.aot_tests.length + ts.tests.symbolic_tests.length + ts.tests.symbolic_execs.length;

        process.stdout.write("--------\n");
        process.stdout.write(`Running ${chalk.bold(ts.src)} suite with ${chalk.bold(totaltests.toString())} tests...\n`);

        const tsstring = new Date().toISOString().slice(0, -5);
        const start = Date.now();

        let tresults: string[] = [];
        let fail = 0;

        for(let i = 0; i < ts.tests.compiler_tests.length; ++i) {
            const ctest = ts.tests.compiler_tests[i];
            const testsrc = Path.normalize(Path.join(__dirname, "tests", ts.src));

            if(singletest !== undefined && singletest != ctest.name) {
                continue;
            }

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
            const testsrc = Path.normalize(Path.join(__dirname, "tests", ts.src));

            if(singletest !== undefined && singletest != ctest.name) {
                continue;
            }

            process.stdout.write(`Running ${ctest.name}...`);
            const tstart = Date.now();

            const cr = this.runAOTTest(testsrc, ctest);
            if (ctest.expected === cr || (ctest.expected === null && (cr.includes("abort") || cr.includes("assert") || cr.includes("check") || cr.includes("Invariant") || cr.includes("pre-condition") || cr.includes("post-condition")))) {
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
            const testsrc = Path.normalize(Path.join(__dirname, "tests", ts.src));

            if(singletest !== undefined && singletest != vtest.name) {
                continue;
            }

            process.stdout.write(`Running ${vtest.name}...`);
            const tstart = Date.now();

            const cr = this.runSymbolicCheckTest(testsrc, vtest);
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

        for(let i = 0; i < ts.tests.symbolic_execs.length; ++i) {
            const vtest = ts.tests.symbolic_execs[i];
            const testsrc = Path.normalize(Path.join(__dirname, "tests", ts.src));

            if(singletest !== undefined && singletest != vtest.name) {
                continue;
            }

            process.stdout.write(`Running ${vtest.name}...`);
            const tstart = Date.now();

            const cr = this.runSymbolicExecTest(testsrc, vtest);
            if (vtest.expected === cr || (vtest.expected === null && cr.includes("unsat"))) {
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
        const rootdir = process.cwd();
        let fail = 0;

        let tr = [];
        for (let i = 0; i < this.tests.length; ++i) {
            const results = this.runTestSet(this.tests[i], i);
            if (results.failed !== 0) {
                fail++;
            }

            tr.push(results.results);
        }

        process.chdir(rootdir);
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

    runner.loadTestSet("doc_examples");
    runner.loadTestSet("apps");
    
    //runner.loadTestSet("expression");
    //runner.loadTestSet("types");
    //runner.loadTestSet("statement");
    
    runner.loadTestSet("library");

    runner.run();
}

////
//Entrypoint

const singletest = process.argv[2];

setImmediate(() => runAll());
