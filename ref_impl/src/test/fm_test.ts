//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { TestInfo } from "./test_runner";
import { MIRAssembly, PackageConfig } from "../compiler/mir_assembly";
import { MIREmitter } from "../compiler/mir_emitter";
import { SMTLIBGenerator } from "../analysis/smtlib/generator";

import * as Path from "path";
import { execSync } from "child_process";

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

const smt2enc_test = `
namespace NSTestSMT2Encode;

entrypoint function add(x: Int, y: Int): Int {
    return x + y;
}

entrypoint function addOpt1(x: [Int, ?: Int]): Int {
    return x.0 + (x.1 ?| 0);
}

function abs(x: Int): Int {
    if(x < 0) {
        return -x;
    }
    else {
        return x;
    }
}

entrypoint function absOpt(x?: Int): Int {
    if(x == none) {
        return 0;
    }

    return abs(x);
}

//entrypoint function max(x: Int, y: Int): Int {
//    if(x > y) {
//        return x;
//    }
//    else {
//        return y;
//    }
//}

entrypoint function maxTuple(x: [Int, Int]): Int {
    if(x.0 > x.1) {
        return x.0;
    }
    else {
        return x.1;
    }
}

entrypoint function swapTuple(x: [Int, Int]): [Int, Int] {
    return [x.1, x.0];
}
`;

const smt2enc_tests: TestInfo[] = [
    {
        name: "add_SAT",
        input: [
            "(declare-const res Int)",
            "(assert (= res (Result_Int@result_value (NSTestSMT2Encode@add 1 3))))",
            "(check-sat)",
            "(get-model)"
        ],
        expected: `sat (model (define-fun res () Int 4) )`
    },
    {
        name: "add_BADASRT",
        input: [
            "(declare-const p1 Int)",
            "(declare-const p2 Int)",
            "(declare-const res Int)",
            "(assert (= res (Result_Int@result_value (NSTestSMT2Encode@add p1 p2))))",
            "(assert (not (and (>= res p1) (>= res p2))))",
            "(check-sat)"
        ],
        expected: `sat`
    },
    {
        name: "addOpt1_SAT",
        input: [
            "(declare-const res Int)",
            "(assert (= res (Result_Int@result_value (NSTestSMT2Encode@addOpt1 (bsq_term_tuple 2 (store (store ((as const (Array Int BTerm)) bsq_term_none) 0 (bsq_term_int 1)) 1 (bsq_term_int 3)))))))",
            "(check-sat)",
            "(get-model)"
        ],
        expected: `sat (model (define-fun res () Int 4) )`
    },
    {
        name: "addOpt1_CHK",
        input: [
            "(declare-const p1 Int)",
            "(declare-const res Int)",
            "(assert (= res (Result_Int@result_value (NSTestSMT2Encode@addOpt1 (bsq_term_tuple 2 (store ((as const (Array Int BTerm)) bsq_term_none) 0 (bsq_term_int p1)))))))",
            "(assert (not (= res p1)))",
            "(check-sat)"
        ],
        expected: `unsat`
    },
    {
        name: "absOpt_CHK_1",
        input: [
            "(declare-const res Int)",
            "(assert (= res (Result_Int@result_value (NSTestSMT2Encode@absOpt bsq_term_none))))",
            "(assert (not (= res 0)))",
            "(check-sat)"
        ],
        expected: `unsat`
    },
    {
        name: "absOpt_CHK_2",
        input: [
            "(declare-const p1 BTerm)",
            "(declare-const res Int)",
            "(assert (is-bsq_term_int p1))",
            "(assert (= res (Result_Int@result_value (NSTestSMT2Encode@absOpt p1))))",
            "(assert (not (>= res (bsq_term_int_value p1))))",
            "(check-sat)"
        ],
        expected: `unsat`
    },
    {
        name: "add_SAT",
        input: [
            "(declare-const res Int)",
            "(assert (= res (Result_Int@result_value (NSTestSMT2Encode@add 1 3))))",
            "(check-sat)",
            "(get-model)"
        ],
        expected: `sat (model (define-fun res () Int 4) )`
    },

    {
        name: "maxTuple_EXEC",
        input: [
            "(declare-const res Int)",
            "(assert (= res (Result_Int@result_value (NSTestSMT2Encode@maxTuple (bsq_tuple$_Int$Int_$ 1 3)))))",
            "(check-sat)",
            "(get-model)"
        ],
        expected: `sat (model (define-fun res () Int 3) )`
    },
    {
        name: "maxTuple_CHK",
        input: [
            "(declare-const p1 Int)",
            "(declare-const p2 Int)",
            "(declare-const res Int)",
            "(assert (= res (Result_Int@result_value (NSTestSMT2Encode@maxTuple (bsq_tuple$_Int$Int_$ p1 p2)))))",
            "(assert (not (and (>= res p1) (>= res p2) (or (= res p1) (= res p2)))))",
            "(check-sat)"
        ],
        expected: `unsat`
    },
    {
        name: "swapTuple_EXEC",
        input: [
            "(declare-const p1 Int)",
            "(assert (= (bsq_tuple$_Int$Int_$ p1 1) (Result_Tbsq_tuple$_Int$Int_$@result_value (NSTestSMT2Encode@swapTuple (bsq_tuple$_Int$Int_$ 1 3)))))",
            "(check-sat)",
            "(get-model)"
        ],
        expected: `sat (model (define-fun p1 () Int 3) )`
    },
    {
        name: "swapTuple_CHK",
        input: [
            "(declare-const p1 Int)",
            "(declare-const p2 Int)",
            "(declare-const r1 Int)",
            "(declare-const r2 Int)",
            "(assert (= (bsq_tuple$_Int$Int_$ r1 r2) (Result_Tbsq_tuple$_Int$Int_$@result_value (NSTestSMT2Encode@swapTuple (bsq_tuple$_Int$Int_$ p1 p2)))))",
            "(assert (not (and (= r1 p2) (= r2 p1))))",
            "(check-sat)"
        ],
        expected: `unsat`
    }
];

function smt2enc_setup(core: { relativePath: string, contents: string }[]): { masm: MIRAssembly | undefined, errors: string[] } {
    const files = core.concat([{ relativePath: "smt2enc_test.bsq", contents: smt2enc_test }]);

    return MIREmitter.generateMASM(new PackageConfig(), files);
}

function runz3(smtlib: string): string {
    try {
        const res = execSync(`${z3path} -smt2 -in `, { input: smtlib });
        return res.toString().replace(/\s{2,}/g, " ").trim();
    }
    catch (ex) {
        console.log(smtlib);
        return `[${ex}]`;
    }
}

function smt2enc_action(assembly: MIRAssembly, args: any[]): any {
    const smt2 = SMTLIBGenerator.generateSMTAssembly(assembly) + "\n\n" + args.join("\n");
    return runz3(smt2);
}

const testSMT2Enc = { name: "SMT2Encode", setup: smt2enc_setup, action: smt2enc_action, tests: smt2enc_tests, xmlid: "SMT2EncodeUnitTests" };

export { testSMT2Enc };
