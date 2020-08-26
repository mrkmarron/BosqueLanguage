//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { Assembly, NamespaceOperatorDecl } from "./assembly";
import { NominalTypeSignature, TypeSignature, AutoTypeSignature } from "./type_signature";

class FunctionScope {
    private readonly m_rtype: TypeSignature;
    private m_captured: Set<string>;
    private m_inImplicitValueBind: boolean;
    private readonly m_ispcode: boolean;
    private readonly m_args: Set<string>;
    private m_locals: Set<string>[];

    constructor(args: Set<string>, rtype: TypeSignature, ispcode: boolean) {
        this.m_rtype = rtype;
        this.m_captured = new Set<string>();
        this.m_inImplicitValueBind = false;
        this.m_ispcode = ispcode;
        this.m_args = args;
        this.m_locals = [];
    }

    pushLocalScope() {
        this.m_locals.push(new Set<string>());
    }

    popLocalScope() {
        this.m_locals.pop();
    }

    isPCodeEnv(): boolean {
        return this.m_ispcode;
    }

    setImplicitValueState(vs: boolean) {
        this.m_inImplicitValueBind = vs;
    }

    isVarNameDefined(name: string): boolean {
        if (this.m_locals.some((frame) => frame.has(name))) {
            return true;
        }

        return this.m_args.has(name) || this.m_captured.has(name);
    }

    defineLocalVar(name: string) {
        this.m_locals[this.m_locals.length - 1].add(name);
    }

    useLocalVar(name: string) {
        if (this.isVarNameDefined(name) || !this.isPCodeEnv()) {
            return;
        }

        if(name !== "$value") {
            this.m_captured.add(name);
        }
        else {
            if(!this.m_inImplicitValueBind) {
                this.m_captured.add(name);
            }
        }
    }

    getCaptureVars(): Set<string> {
        return this.m_captured;
    }

    getReturnType(): TypeSignature {
        return this.m_rtype;
    }
}

class ParserEnvironment {
    private m_currentFile: string | undefined;
    private m_currentNamespace: string | undefined;

    private m_functionScopes: FunctionScope[];

    readonly assembly: Assembly;

    readonly SpecialAnySignature: TypeSignature;
    readonly SpecialNoneSignature: TypeSignature;
    readonly SpecialBoolSignature: TypeSignature;
    
    readonly SpecialIntSignature: TypeSignature;
    readonly SpecialNatSignature: TypeSignature;
    readonly SpecialFloatSignature: TypeSignature;
    readonly SpecialDecimalSignature: TypeSignature;
    readonly SpecialQuadFloatSignature: TypeSignature;
    readonly SpecialBigIntSignature: TypeSignature;
    readonly SpecialBigNatSignature: TypeSignature;
    readonly SpecialRationalSignature: TypeSignature;

    readonly SpecialAutoSignature: TypeSignature;

    constructor(assembly: Assembly) {
        this.m_currentFile = undefined;
        this.m_currentNamespace = undefined;

        this.assembly = assembly;

        this.m_functionScopes = [];

        this.SpecialAnySignature = new NominalTypeSignature("NSCore", ["Any"], []);
        this.SpecialNoneSignature = new NominalTypeSignature("NSCore", ["None"], []);
        this.SpecialBoolSignature = new NominalTypeSignature("NSCore", ["Bool"], []);

        this.SpecialIntSignature = new NominalTypeSignature("NSCore", ["Int"], []);
        this.SpecialNatSignature = new NominalTypeSignature("NSCore", ["Nat"], []);
        this.SpecialFloatSignature = new NominalTypeSignature("NSCore", ["Float64"], []);
        this.SpecialDecimalSignature = new NominalTypeSignature("NSCore", ["Decimal"], []);
        this.SpecialQuadFloatSignature = new NominalTypeSignature("NSCore", ["Float128"], []);
        this.SpecialBigIntSignature = new NominalTypeSignature("NSCore", ["BigInt"], []);
        this.SpecialBigNatSignature = new NominalTypeSignature("NSCore", ["BigNat"], []);
        this.SpecialRationalSignature = new NominalTypeSignature("NSCore", ["Rational"], []);

        this.SpecialAutoSignature = new AutoTypeSignature();
    }

    getCurrentFunctionScope(): FunctionScope {
        return this.m_functionScopes[this.m_functionScopes.length - 1];
    }

    pushFunctionScope(scope: FunctionScope) {
        this.m_functionScopes.push(scope);
    }

    popFunctionScope(): FunctionScope {
        return this.m_functionScopes.pop() as FunctionScope;
    }

    setNamespaceAndFile(ns: string, file: string) {
        this.m_currentFile = file;
        this.m_currentNamespace = ns;
    }

    getCurrentFile(): string {
        return this.m_currentFile as string;
    }

    getCurrentNamespace(): string {
        return this.m_currentNamespace as string;
    }

    isVarDefinedInAnyScope(name: string): boolean {
        return this.m_functionScopes.some((sc) => sc.isVarNameDefined(name));
    }

    tryResolveNamespace(ns: string | undefined, typename: string): string | undefined {
        if (ns !== undefined) {
            return ns;
        }

        const coredecl = this.assembly.getNamespace("NSCore");
        if (coredecl.declaredNames.has("NSCore::" + typename)) {
            return "NSCore";
        }
        else {
            const nsdecl = this.assembly.getNamespace(this.m_currentNamespace as string);
            if (nsdecl.declaredNames.has(this.m_currentNamespace + "::" + typename)) {
                return this.m_currentNamespace as string;
            }
            else {
                const fromns = nsdecl.usings.find((nsuse) => nsuse.names.indexOf(typename) !== -1);
                return fromns !== undefined ? fromns.fromNamespace : undefined;
            }
        }
    }

    tryResolveAsPrefixUnaryOperator(opname: string, level: number): string | undefined {
        const nsdecl = this.assembly.getNamespace(this.m_currentNamespace as string);
        if (nsdecl.declaredNames.has(this.m_currentNamespace + "::" + opname) && nsdecl.operators.get(opname) !== undefined) {
            const opdecls = nsdecl.operators.get(opname) as NamespaceOperatorDecl[];
            return opdecls.some((opdecl) => (opdecl.isPrefix && opdecl.level === level)) ? this.m_currentNamespace as string : undefined;
        }

        const fromns = nsdecl.usings.find((nsuse) => nsuse.names.indexOf(opname) !== -1);
        return fromns !== undefined ? fromns.fromNamespace : undefined;
    }

    tryResolveAsInfixBinaryOperator(opname: string, level: number): string | undefined {
        const nsdecl = this.assembly.getNamespace(this.m_currentNamespace as string);
        if (nsdecl.declaredNames.has(this.m_currentNamespace + "::" + opname) && nsdecl.operators.get(opname) !== undefined) {
            const opdecls = nsdecl.operators.get(opname) as NamespaceOperatorDecl[];
            return opdecls.some((opdecl) => (opdecl.isInfix && opdecl.level === level)) ? this.m_currentNamespace as string : undefined;
        }

        const fromns = nsdecl.usings.find((nsuse) => nsuse.names.indexOf(opname) !== -1);
        return fromns !== undefined ? fromns.fromNamespace : undefined;
    }
}

export { FunctionScope, ParserEnvironment };
