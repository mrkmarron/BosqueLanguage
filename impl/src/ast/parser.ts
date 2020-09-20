//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ParserEnvironment, FunctionScope } from "./parser_env";
import { FunctionParameter, TypeSignature, NominalTypeSignature, TemplateTypeSignature, ParseErrorTypeSignature, TupleTypeSignature, RecordTypeSignature, FunctionTypeSignature, UnionTypeSignature, AutoTypeSignature, ProjectTypeSignature, EphemeralListTypeSignature, PlusTypeSignature, AndTypeSignature, LiteralTypeSignature } from "./type_signature";
import { Arguments, TemplateArguments, NamedArgument, PositionalArgument, InvalidExpression, Expression, LiteralNoneExpression, LiteralBoolExpression, LiteralIntegerExpression, LiteralStringExpression, LiteralTypedStringExpression, AccessVariableExpression, AccessNamespaceConstantExpression, LiteralTypedStringConstructorExpression, CallNamespaceFunctionOrOperatorExpression, AccessStaticFieldExpression, ConstructorTupleExpression, ConstructorRecordExpression, ConstructorPrimaryExpression, ConstructorPrimaryWithFactoryExpression, PostfixOperation, PostfixAccessFromIndex, PostfixAccessFromName, PostfixProjectFromIndecies, PostfixProjectFromNames, PostfixModifyWithIndecies, PostfixModifyWithNames, PostfixInvoke, PostfixOp, PrefixNotOp, BinLogicExpression, NonecheckExpression, CoalesceExpression, SelectExpression, BlockStatement, Statement, BodyImplementation, EmptyStatement, InvalidStatement, VariableDeclarationStatement, VariableAssignmentStatement, ReturnStatement, YieldStatement, CondBranchEntry, IfElse, IfElseStatement, InvokeArgument, CallStaticFunctionOrOperatorExpression, AssertStatement, CheckStatement, DebugStatement, StructuredAssignment, TupleStructuredAssignment, RecordStructuredAssignment, VariableDeclarationStructuredAssignment, IgnoreTermStructuredAssignment, VariableAssignmentStructuredAssignment, ConstValueStructuredAssignment, StructuredVariableAssignmentStatement, MatchStatement, MatchEntry, MatchGuard, WildcardMatchGuard, StructureMatchGuard, AbortStatement, BlockStatementExpression, IfExpression, MatchExpression, PragmaArguments, ConstructorPCodeExpression, PCodeInvokeExpression, ExpOrExpression, LiteralRegexExpression, ValidateStatement, NakedCallStatement, ValueListStructuredAssignment, NominalStructuredAssignment, VariablePackDeclarationStatement, VariablePackAssignmentStatement, ConstructorEphemeralValueList, LiteralBigIntegerExpression, LiteralFloatExpression, MapEntryConstructorExpression, LiteralParamerterValueExpression, SpecialConstructorExpression, TypeMatchGuard, PostfixIs, LiteralDecimalExpression, LiteralNaturalExpression, LiteralBigNaturalExpression, LiteralRationalExpression, LiteralTypedNumericConstructorExpression, PostfixHasIndex, PostfixHasProperty, PostfixAs, BinEqExpression, BinCmpExpression } from "./body";
import { Assembly, NamespaceUsing, NamespaceDeclaration, NamespaceTypedef, StaticMemberDecl, StaticFunctionDecl, MemberFieldDecl, MemberMethodDecl, ConceptTypeDecl, EntityTypeDecl, NamespaceConstDecl, NamespaceFunctionDecl, InvokeDecl, TemplateTermDecl, PreConditionDecl, PostConditionDecl, BuildLevel, TypeConditionRestriction, InvariantDecl, TemplateTypeRestriction, SpecialTypeCategory, StaticOperatorDecl, NamespaceOperatorDecl, OOPTypeDecl, TemplateTermSpecialRestriction } from "./assembly";
import { BSQRegex } from "./bsqregex";
import { MIRNominalType } from "../compiler/mir_assembly";

const KeywordStrings = [
    "pragma",

    "struct",
    "hidden",
    "private",
    "factory",
    "virtual",
    "abstract",
    "override",
    "entrypoint",
    "recursive?",
    "recursive",
    "parsable",
    "validator",
    "memoized",
    "inline",
    "prefix",
    "infix",
    "dynamic",

    "_debug",
    "abort",
    "assert",
    "case",
    "check",
    "concept",
    "const",
    "elif",
    "else",
    "empty",
    "enum",
    "entity",
    "ensures",
    "err",
    "false",
    "field",
    "fn",
    "function",
    "grounded",
    "identifier",
    "if",
    "invariant",
    "let",
    "method",
    "namespace",
    "none",
    "ok",
    "operator",
    "or",
    "private",
    "provides",
    "ref",
    "release",
    "return",
    "requires",
    "switch",
    "test",
    "true",
    "type",
    "typedef",
    "unique",
    "unit",
    "validate",
    "var",
    "when",
    "where",
    "yield"
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : a.localeCompare(b); });

const SymbolStrings = [
    "[",
    "(",
    "{",
    "]",
    ")",
    "}",
    "(|",
    "|)",
    "{|",
    "|}",

    "#",
    "&",
    "&&",
    "@",
    "!",
    "!=",
    ":",
    "::",
    ",",
    ".",
    "...",
    "=",
    "==",
    "=>",
    "==>",
    ";",
    "|",
    "||",
    "+",
    "?",
    "?&",
    "?|",
    "?.",
    "<",
    "<=",
    ">",
    ">=",
    "-",
    "->",
    "*",
    "/"
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : a.localeCompare(b); });

const RegexFollows = new Set<string>([
    "_debug",
    "abort",
    "assert",
    "check",
    "else",
    "ensures",
    "invariant",
    "or",
    "release",
    "return",
    "requires",
    "test",
    "validate",
    "when",
    "yield",
    "[",
    "]",
    "(",
    "{",
    "(|",
    "{|",
    "&&",
    "!",
    "!=",
    ",",
    "=",
    "==",
    "=>",
    "==>",
    ";",
    "||",
    "+",
    "?&",
    "?|",
    "<",
    "<=",
    ">",
    ">=",
    "-",
    "*",
    "/"
]);

const LeftScanParens = ["[", "(", "{", "(|", "{|"];
const RightScanParens = ["]", ")", "}", "|)", "|}"];

const AttributeStrings = ["inline", "struct", "hidden", "private", "factory", "virtual", "abstract", "override", "entrypoint", "recursive?", "recursive", "parsable", "memoized", "grounded", "prefix", "infix", "dynamic"];

const UnsafeFieldNames = ["is", "as", "tryAs", "isNone", "isSome", "update", "hasProperty"]

const TokenStrings = {
    Clear: "[CLEAR]",
    Error: "[ERROR]",

    Int: "[LITERAL_INT]",
    Nat: "[LITERAL_NAT]",
    Float: "[LITERAL_FLOAT]",
    Decimal: "[LITERAL_DECIMAL]",
    BigInt: "[LITERAL_BIGINT]",
    BigNat: "[LITERAL_BIGNAT]",
    Rational: "[LITERAL_RATIONAL]",
    String: "[LITERAL_STRING]",
    Regex: "[LITERAL_REGEX]",
    TypedString: "[LITERAL_TYPED_STRING]",
    TypedInt: "[LITERAL_TYPED_INT]",
    TypedBigInt: "[LITERAL_TYPED_BIGINT]",
    TypedFloat: "[LITERAL_TYPED_FLOAT]",

    //Names
    Namespace: "[NAMESPACE]",
    Type: "[TYPE]",
    Template: "[TEMPLATE]",
    Identifier: "[IDENTIFIER]",
    Operator: "[OPERATOR]",

    EndOfStream: "[EOS]"
};

class Token {
    readonly line: number;
    readonly column: number;
    readonly pos: number;
    readonly span: number;

    readonly kind: string;
    readonly data: string | undefined;

    constructor(line: number, column: number, cpos: number, span: number, kind: string, data?: string) {
        this.line = line;
        this.column = column;
        this.pos = cpos;
        this.span = span;

        this.kind = kind;
        this.data = data;
    }
}

class SourceInfo {
    readonly line: number;
    readonly column: number;
    readonly pos: number;
    readonly span: number;

    constructor(line: number, column: number, cpos: number, span: number) {
        this.line = line;
        this.column = column;
        this.pos = cpos;
        this.span = span;
    }
}

function unescapeLiteralString(str: string): string {
    let rs = str
        .replace(/\\0/ug, "\0")
        .replace(/\\'/ug, "'")
        .replace(/\\"/ug, "\"")
        .replace(/\\n/ug, "\n")
        .replace(/\\r/ug, "\r")
        .replace(/\\t/ug, "\t");

    let mm = rs.match(/\\u\{([0-9A-Fa-f])+\}/u);
    while(mm !== null) {
        const ccode = Number.parseInt(mm[1], 16);
        const charstr = String.fromCodePoint(ccode);
        rs = rs.slice(0, mm.index as number) + charstr + rs.slice(mm.index as number + mm[0].length);
    }

    return rs.replace(/\\\\/ug, "\\");
}

class Lexer {
    private static findSymbolString(str: string): string | undefined {
        if(str.startsWith("$") && !/^([$][_\p{L}])/.test(str)) {
            return "$";
        }

        return SymbolStrings.find((value) => str.startsWith(value));
    }

    private static findKeywordString(str: string): string | undefined {
        let imin = 0;
        let imax = KeywordStrings.length;

        while (imin < imax) {
            const imid = Math.floor((imin + imax) / 2);

            const scmpval = (str.length !== KeywordStrings[imid].length) ? (KeywordStrings[imid].length - str.length) : str.localeCompare(KeywordStrings[imid]);
            if (scmpval === 0) {
                return KeywordStrings[imid];
            }
            else if (scmpval < 0) {
                imax = imid;
            }
            else {
                imin = imid + 1;
            }
        }
        return undefined;
    }

    private m_input: string;
    private m_internTable: Map<string, string>;
    private m_cline: number;
    private m_linestart: number;
    private m_cpos: number;
    private m_tokens: Token[];

    constructor(input: string) {
        this.m_input = input;
        this.m_internTable = new Map<string, string>();
        this.m_cline = 1;
        this.m_linestart = 0;
        this.m_cpos = 0;
        this.m_tokens = [];
    }

    ////
    //Helpers
    private static isNamespaceName(str: string) {
        return /^NS/.test(str);
    }

    private static isTypenameName(str: string) {
        return str.length > 1 && !/^NS/.test(str) && /^[A-Z]/.test(str);
    }

    private static isTemplateName(str: string) {
        return str.length === 1 && /^[A-Z]$/.test(str);
    }

    //TODO: we need to make sure that someone doesn't name a local variable "_"
    private static isIdentifierName(str: string) {
        return /^([$]?([_\p{L}][_\p{L}\p{Nd}]*))$/u.test(str);
    }

    private recordLexToken(epos: number, kind: string) {
        this.m_tokens.push(new Token(this.m_cline, this.m_cpos - this.m_linestart, this.m_cpos, epos - this.m_cpos, kind, kind)); //set data to kind string
        this.m_cpos = epos;
    }

    private recordLexTokenWData(epos: number, kind: string, data: string) {
        const rdata = this.m_internTable.get(data) || this.m_internTable.set(data, data).get(data);
        this.m_tokens.push(new Token(this.m_cline, this.m_cpos - this.m_linestart, this.m_cpos, epos - this.m_cpos, kind, rdata));
        this.m_cpos = epos;
    }

    private static readonly _s_whitespaceRe = /\p{Z}+/uy;
    private tryLexWS(): boolean {
        Lexer._s_whitespaceRe.lastIndex = this.m_cpos;
        const m = Lexer._s_whitespaceRe.exec(this.m_input);
        if (m === null) {
            return false;
        }

        for (let i = 0; i < m[0].length; ++i) {
            if (m[0][i] === "\n") {
                this.m_cline++;
                this.m_linestart = this.m_cpos + i + 1;
            }
        }

        this.m_cpos += m[0].length;
        return true;
    }

    private static readonly _s_commentRe = /(\/\/.*)|(\/\*[\p{L}\p{M}\p{N}\p{S}\p{Z}]*?\*\/)/uy;
    private tryLexComment(): boolean {
        Lexer._s_commentRe.lastIndex = this.m_cpos;
        const m = Lexer._s_commentRe.exec(this.m_input);
        if (m === null) {
            return false;
        }

        for (let i = 0; i < m[0].length; ++i) {
            if (m[0][i] === "\n") {
                this.m_cline++;
                this.m_linestart = this.m_cpos + i + 1;
            }
        }

        this.m_cpos += m[0].length;
        return true;
    }

    private static readonly _s_intRe = /(0|[1-9][0-9]*)/y;
    private static readonly _s_natRe = /(0|[1-9][0-9]*)n/y;

    private static readonly _s_floatRe = /([0-9]+\.[0-9]+)([eE][-+]?[0-9]+)?/y;
    private static readonly _s_decimalRe = /([0-9]+\.[0-9]+)([eE][-+]?[0-9]+)?d/y;

    private static readonly _s_bigintRe = /(0|[1-9][0-9]*)I/y;
    private static readonly _s_bignatRe = /(0|[1-9][0-9]*)N/y;
    private static readonly _s_rationalRe = /(0|[1-9][0-9]*)|((0|[1-9][0-9]*))\/(0|[1-9][0-9]*))R/y;

    private tryLexNumber(): boolean {
        Lexer._s_rationalRe.lastIndex = this.m_cpos;
        const mr = Lexer._s_rationalRe.exec(this.m_input);
        if (mr !== null) {
            this.recordLexTokenWData(this.m_cpos + mr[0].length, TokenStrings.Rational, mr[0]);
            return true;
        }

        Lexer._s_bignatRe.lastIndex = this.m_cpos;
        const mbn = Lexer._s_bignatRe.exec(this.m_input);
        if (mbn !== null) {
            this.recordLexTokenWData(this.m_cpos + mbn[0].length, TokenStrings.BigNat, mbn[0]);
            return true;
        }

        Lexer._s_bigintRe.lastIndex = this.m_cpos;
        const mbi = Lexer._s_bigintRe.exec(this.m_input);
        if (mbi !== null) {
            this.recordLexTokenWData(this.m_cpos + mbi[0].length, TokenStrings.BigInt, mbi[0]);
            return true;
        }

        Lexer._s_decimalRe.lastIndex = this.m_cpos;
        const md = Lexer._s_decimalRe.exec(this.m_input);
        if (md !== null) {
            this.recordLexTokenWData(this.m_cpos + md[0].length, TokenStrings.Decimal, md[0]);
            return true;
        }

        Lexer._s_floatRe.lastIndex = this.m_cpos;
        const mf = Lexer._s_floatRe.exec(this.m_input);
        if (mf !== null) {
            this.recordLexTokenWData(this.m_cpos + mf[0].length, TokenStrings.Float, mf[0]);
            return true;
        }

        Lexer._s_natRe.lastIndex = this.m_cpos;
        const mn = Lexer._s_natRe.exec(this.m_input);
        if (mn !== null) {
            this.recordLexTokenWData(this.m_cpos + mn[0].length, TokenStrings.Nat, mn[0]);
            return true;
        }

        Lexer._s_intRe.lastIndex = this.m_cpos;
        const mi = Lexer._s_intRe.exec(this.m_input);
        if (mi !== null) {
            this.recordLexTokenWData(this.m_cpos + mi[0].length, TokenStrings.Int, mi[0]);
            return true;
        }

        return false;
    }

    private static readonly _s_stringRe = /"[^"\\\r\n]*(\\(.|\r?\n)[^"\\\r\n]*)*"/uy;
    private static readonly _s_typedStringRe = /'[^'\\\r\n]*(\\(.|\r?\n)[^'\\\r\n]*)*'/uy;
    private tryLexString() {
        Lexer._s_stringRe.lastIndex = this.m_cpos;
        const ms = Lexer._s_stringRe.exec(this.m_input);
        if (ms !== null) {
            this.recordLexTokenWData(this.m_cpos + ms[0].length, TokenStrings.String, ms[0]);
            return true;
        }

        Lexer._s_typedStringRe.lastIndex = this.m_cpos;
        const mts = Lexer._s_typedStringRe.exec(this.m_input);
        if (mts !== null) {
            this.recordLexTokenWData(this.m_cpos + mts[0].length, TokenStrings.TypedString, mts[0]);
            return true;
        }

        return false;
    }

    private static readonly _s_regexRe = /\/[^"\\\r\n]*(\\(.)[^"\\\r\n]*)*\//uy;
    private tryLexRegex() {
        Lexer._s_regexRe.lastIndex = this.m_cpos;
        const ms = Lexer._s_regexRe.exec(this.m_input);
        if (ms !== null && RegexFollows.has(this.m_tokens[this.m_tokens.length - 1].kind)) {
            this.recordLexTokenWData(this.m_cpos + ms[0].length, TokenStrings.Regex, ms[0]);
            return true;
        }

        return false;
    }

    private static readonly _s_symbolRe = /[\W]+/y;
    private static readonly _s_operatorRe = /[\p{Sm}\p{So}]/uy;
    private tryLexSymbol() {
        Lexer._s_symbolRe.lastIndex = this.m_cpos;
        const ms = Lexer._s_symbolRe.exec(this.m_input);
        if (ms === null) {
            return false;
        }

        const sym = Lexer.findSymbolString(ms[0]);
        if (sym !== undefined) {
            this.recordLexToken(this.m_cpos + sym.length, sym);
            return true;
        }

        Lexer._s_operatorRe.lastIndex = this.m_cpos;
        const mo = Lexer._s_operatorRe.exec(this.m_input);
        if (mo !== null) {
            const oper = mo[0];
            this.recordLexTokenWData(this.m_cpos + oper.length, TokenStrings.Operator, oper);
            return true;
        }

        return false;
    }

    private static readonly _s_nameRe = /([$]?[_\p{L}][_\p{L}\p{Nd}]+)|(recursive\?)/uy;
    private tryLexName(): boolean {
        if (this.m_input.startsWith("recursive?", this.m_cpos)) {
            this.recordLexToken(this.m_cpos + "recursive?".length, "recursive?");
            return true;
        }

        Lexer._s_nameRe.lastIndex = this.m_cpos;
        const m = Lexer._s_nameRe.exec(this.m_input);
        if (m === null) {
            return false;
        }

        const name = m[0];

        const kwmatch = Lexer.findKeywordString(name);
        if (kwmatch) {
            this.recordLexToken(this.m_cpos + name.length, kwmatch);
            return true;
        }
        else if (Lexer.isNamespaceName(name)) {
            this.recordLexTokenWData(this.m_cpos + name.length, TokenStrings.Namespace, name);
            return true;
        }
        else if (Lexer.isTypenameName(name)) {
            this.recordLexTokenWData(this.m_cpos + name.length, TokenStrings.Type, name);
            return true;
        }
        else if (Lexer.isTemplateName(name)) {
            this.recordLexTokenWData(this.m_cpos + name.length, TokenStrings.Template, name);
            return true;
        }
        else if (Lexer.isIdentifierName(name)) {
            this.recordLexTokenWData(this.m_cpos + name.length, TokenStrings.Identifier, name);
            return true;
        }
        else {
            this.recordLexToken(this.m_cpos + name.length, TokenStrings.Error);
            return false;
        }
    }

    static isAttributeKW(str: string) {
        return AttributeStrings.indexOf(str) !== -1;
    }

    lex(): Token[] {
        if (this.m_tokens.length !== 0) {
            return this.m_tokens;
        }

        this.m_tokens = [];
        while (this.m_cpos < this.m_input.length) {
            if (this.tryLexWS() || this.tryLexComment()) {
                //continue
            }
            else if (this.tryLexNumber() || this.tryLexString() || this.tryLexRegex() || this.tryLexSymbol() || this.tryLexName()) {
                //continue
            }
            else {
                this.recordLexToken(this.m_cpos + 1, TokenStrings.Error);
            }
        }

        this.recordLexToken(this.m_input.length, TokenStrings.EndOfStream);
        return this.m_tokens;
    }
}

class ParseError extends Error {
    constructor(line: number, message?: string) {
        super(`Parse failure on line ${line} -- ${message}`);
        Object.setPrototypeOf(this, new.target.prototype);
    }
}

enum InvokableKind {
    Basic,
    Member,
    PCode,
    StaticOperator,
    DynamicOperator
}

class Parser {
    private m_tokens: Token[];
    private m_cpos: number;
    private m_epos: number;

    private m_penv: ParserEnvironment;

    private m_errors: [string, number, string][];
    private m_recoverStack: number[];

    constructor(assembly: Assembly) {
        this.m_tokens = [];
        this.m_cpos = 0;
        this.m_epos = 0;

        this.m_penv = new ParserEnvironment(assembly);
        this.m_errors = [];
        this.m_recoverStack = [];
    }

    private initialize(toks: Token[]) {
        this.m_tokens = toks;
        this.m_cpos = 0;
        this.m_epos = toks.length;
    }

    ////
    //Helpers

    private static attributeSetContains(attr: string, attribs: string[]): boolean {
        return attribs.indexOf(attr) !== -1;
    }

    private getCurrentLine(): number {
        return this.m_tokens[this.m_cpos].line;
    }

    private getCurrentSrcInfo(): SourceInfo {
        const tk = this.m_tokens[this.m_cpos];
        return new SourceInfo(tk.line, 0, tk.pos, tk.span);
    }

    private setRecover(pos: number) {
        this.m_recoverStack.push(pos);
    }

    private clearRecover(pos?: number) {
        this.m_recoverStack.pop();
    }

    private processRecover() {
        this.m_cpos = this.m_recoverStack.pop() as number;
    }

    private raiseError(line: number, msg: string) {
        this.m_errors.push([this.m_penv.getCurrentFile(), line, msg]);
        throw new ParseError(line, msg);
    }

    private scanMatchingParens(lp: string, rp: string): number {
        let pscount = 1;
        for (let pos = this.m_cpos + 1; pos < this.m_epos; ++pos) {
            const tok = this.m_tokens[pos];
            if (tok.kind === lp) {
                pscount++;
            }
            else if (tok.kind === rp) {
                pscount--;
            }
            else {
                //nop
            }

            if (pscount === 0) {
                return pos + 1;
            }
        }

        return this.m_epos;
    }

    private scanCodeParens(): number {
        let pscount = 1;
        for (let pos = this.m_cpos + 1; pos < this.m_epos; ++pos) {
            const tok = this.m_tokens[pos];
            if (LeftScanParens.indexOf(tok.kind) !== -1) {
                pscount++;
            }
            else if (RightScanParens.indexOf(tok.kind) !== -1) {
                pscount--;
            }
            else {
                //nop
            }

            if (pscount === 0) {
                return pos + 1;
            }
        }

        return this.m_epos;
    }

    private setNamespaceAndFile(ns: string, file: string) {
        this.m_penv.setNamespaceAndFile(ns, file);
    }

    private peekToken(pos?: number): string {
        return this.m_tokens[this.m_cpos + (pos || 0)].kind;
    }

    private peekTokenData(pos?: number): string {
        return this.m_tokens[this.m_cpos + (pos || 0)].data as string;
    }

    private testToken(kind: string): boolean {
        return (this.m_cpos !== this.m_epos) && this.m_tokens[this.m_cpos].kind === kind;
    }

    private testFollows(...kinds: string[]): boolean {
        for (let i = 0; i < kinds.length; ++i) {
            if (this.m_cpos + i === this.m_epos || this.m_tokens[this.m_cpos + i].kind !== kinds[i]) {
                return false;
            }
        }

        return true;
    }

    testFollowsFrom(pos: number, ...kinds: string[]): boolean {
        for (let i = 0; i < kinds.length; ++i) {
            if (pos + i === this.m_epos || this.m_tokens[pos + i].kind !== kinds[i]) {
                return false;
            }
        }

        return true;
    }

    private consumeToken() {
        this.m_cpos++;
    }

    private consumeTokenIf(kind: string) {
        if (this.testToken(kind)) {
            this.consumeToken();
        }
    }

    private testAndConsumeTokenIf(kind: string): boolean {
        const test = this.testToken(kind);
        if (test) {
            this.consumeToken();
        }
        return test;
    }

    private consumeTokenAndGetValue(): string {
        const td = this.m_tokens[this.m_cpos].data;
        this.consumeToken();
        return td as string;
    }

    private ensureToken(kind: string) {
        if (!this.testToken(kind)) {
            const found = this.m_tokens[this.m_cpos].data || this.m_tokens[this.m_cpos].kind;
            this.raiseError(this.m_tokens[this.m_cpos].line, `Expected "${kind}" but found "${found}"`);
        }
    }

    private ensureAndConsumeToken(kind: string) {
        this.ensureToken(kind);
        this.consumeToken();
    }

    private ensureNotToken(kind: string) {
        if (this.testToken(kind)) {
            this.raiseError(this.m_tokens[this.m_cpos].line, `Token "${kind}" is not allowed`);
        }
    }

    private scanToken(tok: string): number {
        let pos = this.m_cpos;

        while (pos !== this.m_epos) {
            if (this.m_tokens[pos].kind === tok) {
                return pos;
            }
            pos++;
        }
        return this.m_epos;
    }

    private scanTokenOptions(...toks: string[]): number {
        let pos = this.m_cpos;

        while (pos !== this.m_epos) {
            if (toks.indexOf(this.m_tokens[pos].kind) !== -1) {
                return pos;
            }
            pos++;
        }
        return this.m_epos;
    }

    private parseListOf<T>(start: string, end: string, sep: string, fn: () => T, specialToken?: string): [T[], boolean] {
        let specialFound = false;
        let result: T[] = [];

        this.ensureAndConsumeToken(start);
        while (!this.testAndConsumeTokenIf(end)) {
            if (specialToken !== undefined && this.testAndConsumeTokenIf(specialToken)) {
                specialFound = true;
                this.ensureToken(end);
            }
            else {
                result.push(fn());
            }

            if (this.testAndConsumeTokenIf(sep)) {
                this.ensureNotToken(end);
            }
            else {
                this.ensureToken(end);
            }
        }

        return [result, specialFound];
    }

    private parseEphemeralListOf<T>(fn: () => T): T[] {
        let result: T[] = [];

        while (true) {
            result.push(fn());

            if(!this.testAndConsumeTokenIf(",")) {
                break;
            }
        }

        return result;
    }

    parseBuildInfo(cb: BuildLevel): BuildLevel {
        if(this.testToken("debug") || this.testToken("test") || this.testToken("release")) {
            return this.consumeTokenAndGetValue() as "debug" | "test" | "release";
        }
        else {
            return cb;
        }
    }

    ////
    //Misc parsing

    private parseInvokableCommon(ikind: InvokableKind, noBody: boolean, attributes: string[], isrecursive: "yes" | "no" | "cond", pragmas: [TypeSignature, string][], terms: TemplateTermDecl[], termRestrictions: TypeConditionRestriction | undefined, optSelfType?: TypeSignature): InvokeDecl {
        const sinfo = this.getCurrentSrcInfo();
        const srcFile = this.m_penv.getCurrentFile();
        const line = this.getCurrentLine();

        let fparams: FunctionParameter[] = [];
        if (ikind === InvokableKind.Member) {
            fparams.push(new FunctionParameter("this", optSelfType as TypeSignature, false, false, false, undefined));
        }

        let restName: string | undefined = undefined;
        let restType: TypeSignature | undefined = undefined;
        let resultInfo = this.m_penv.SpecialAutoSignature;

        const params = this.parseListOf<[string, TypeSignature, boolean, boolean, boolean, boolean, Expression | undefined]>("(", ")", ",", () => {
            const isrest = this.testAndConsumeTokenIf("...");
            const isref = this.testAndConsumeTokenIf("ref");

            this.ensureToken(TokenStrings.Identifier);
            const pname = this.consumeTokenAndGetValue();
            const isopt = this.testAndConsumeTokenIf("?");
            let argtype = this.m_penv.SpecialAutoSignature;

            if (this.testAndConsumeTokenIf(":")) {
                argtype = this.parseTypeSignature(ikind === InvokableKind.StaticOperator || ikind === InvokableKind.DynamicOperator);
            }
            else {
                if (ikind !== InvokableKind.PCode) {
                    this.raiseError(line, "Auto typing is not supported for this");
                }
            }

            if (isref && (isopt || isrest)) {
                this.raiseError(line, "Cannot use ref parameters here");
            }

            let exp: Expression | undefined = undefined;
            if(isopt && this.testAndConsumeTokenIf("=")) {
                exp = this.parseExpression();
            }

            let isliteral = false;
            if(this.testAndConsumeTokenIf("==")) {
                if(ikind !== InvokableKind.DynamicOperator) {
                    this.raiseError(line, "Literal parameters are only allowed on dynamic operator definitions");
                }

                isliteral = true;
                exp = this.parseExpression();
            }

            if(ikind === InvokableKind.DynamicOperator || ikind === InvokableKind.StaticOperator) {
                if(isopt || isrest) {
                    this.raiseError(line, "Cannot use opt or rest parameters in operators");
                }
            }

            return [pname, argtype, isopt, isrest, isref, isliteral, exp];
        })[0];

        for (let i = 0; i < params.length; i++) {
            if (!params[i][3]) {
                fparams.push(new FunctionParameter(params[i][0], params[i][1], params[i][2], params[i][4], params[i][5], params[i][6]));
            }
            else {
                if (i + 1 !== params.length) {
                    this.raiseError(line, "Rest parameter must be last in parameter list");
                }

                restName = params[i][0];
                restType = params[i][1];
            }
        }

        if (restName !== undefined && params.some((p) => p[2])) {
            this.raiseError(line, "Cannot have optional and rest parameters in a function");
        }

        if (this.testAndConsumeTokenIf(":")) {
            resultInfo = this.parseResultType(false);
        }
        else {
            if (ikind !== InvokableKind.PCode) {
                if(!params.some((p) => p[4])) {
                    this.raiseError(line, "Cannot have void return unless one of the params is by-ref");
                }
                resultInfo = this.m_penv.SpecialNoneSignature; //void conversion
            }
        }

        const argNames = new Set<string>([...(restName ? [restName] : []), ...fparams.map((param) => param.name)]);
        let preconds: PreConditionDecl[] = [];
        let postconds: PostConditionDecl[] = [];
        let body: BodyImplementation | undefined = undefined;
        let captured = new Set<string>();
        if (noBody) {
            this.ensureAndConsumeToken(";");
        }
        else {
            if (ikind == InvokableKind.PCode) {
                this.ensureAndConsumeToken("=>");
            }
            else {
                [preconds, postconds] = this.parsePreAndPostConditions(sinfo, argNames, resultInfo);
            }

            const bodyid = `${srcFile}::${sinfo.pos}`;
            try {
                this.m_penv.pushFunctionScope(new FunctionScope(argNames, resultInfo, ikind === InvokableKind.PCode));
                body = this.parseBody(bodyid, srcFile);
                captured = this.m_penv.getCurrentFunctionScope().getCaptureVars();
                this.m_penv.popFunctionScope();
            }
            catch (ex) {
                this.m_penv.popFunctionScope();
                throw ex;
            }
        }

        if (ikind === InvokableKind.PCode) {
            return InvokeDecl.createPCodeInvokeDecl(sinfo, srcFile, attributes, isrecursive, fparams, restName, restType, resultInfo, captured, body as BodyImplementation);
        }
        else {
            return InvokeDecl.createStandardInvokeDecl(sinfo, srcFile, attributes, isrecursive, pragmas, terms, termRestrictions, fparams, restName, restType, resultInfo, preconds, postconds, body);
        }
    }

    ////
    //Type parsing

    private parseResultType(parensreq: boolean): TypeSignature {
        if (this.testAndConsumeTokenIf("(|")) {
            const decls = this.parseEphemeralListOf(() => {
                const tdecl = this.parseTypeSignature(false);
                return tdecl;
            });

            this.ensureAndConsumeToken("|)");
            return new EphemeralListTypeSignature(decls);
        }
        else {
            if(parensreq) {
                return this.parseTypeSignature(false);
            }
            else {
                const decls = this.parseEphemeralListOf(() => {
                    const tdecl = this.parseTypeSignature(false);
                    return tdecl;
                });
    
                return decls.length === 1 ? decls[0] : new EphemeralListTypeSignature(decls);
            }
        }
    } 

    private parseTypeSignature(literalTypeOk: boolean): TypeSignature {
        return this.parseOrCombinatorType(literalTypeOk);
    }

    private parseOrCombinatorType(literalTypeOk: boolean): TypeSignature {
        const ltype = this.parsePostfixTypeReference(literalTypeOk);
        if (!this.testToken("|")) {
            return ltype;
        }
        else {
            this.consumeToken();
            return Parser.orOfTypeSignatures(ltype, this.parseOrCombinatorType(false));
        }
    }

    private parsePostfixTypeReference(literalTypeOk: boolean): TypeSignature {
        let roottype = this.parseCombineCombinatorType(literalTypeOk);
        while (this.testToken("?")) {
            if(roottype instanceof LiteralTypeSignature) {
                this.raiseError(this.getCurrentLine(), "Cannot have nonable literal type");
            }

            roottype = this.parseNoneableType(roottype);
        }
        return roottype;
    }

    private parseNoneableType(basetype: TypeSignature): TypeSignature {
        this.ensureAndConsumeToken("?");
        return Parser.orOfTypeSignatures(basetype, this.m_penv.SpecialNoneSignature);
    }

    private parseCombineCombinatorType(literalTypeOk: boolean): TypeSignature {
        const ltype = this.parseProjectType(literalTypeOk);
        if (!this.testToken("&") && !this.testToken("+")) {
            return ltype;
        }
        else {
            if(this.testToken("&")) {
                this.consumeToken();
                return this.andOfTypeSignatures(ltype, this.parseCombineCombinatorType(false));
            }
            else {
                this.consumeToken();
                return this.plusOfTypeSignatures(ltype, this.parseCombineCombinatorType(false));
            }
        }
    }

    private parseProjectType(literalTypeOk: boolean): TypeSignature {
        const ltype = this.parseBaseTypeReference(literalTypeOk);
        if (!this.testToken("!")) {
            return ltype;
        }
        else {
            this.consumeToken();
            const ptype = this.parseNominalType();
            
            return new ProjectTypeSignature(ltype, ptype);
        }
    }

    private parseBaseTypeReference(literalTypeOk: boolean): TypeSignature {
        switch (this.peekToken()) {
            case TokenStrings.Template:
                return this.parseTemplateTypeReference();
            case TokenStrings.Namespace:
            case TokenStrings.Type:
                return this.parseNominalType();
            case "@":
            case "#": { 
                const isvalue = this.testToken("#");
                this.consumeToken();
                if(this.testToken("[")) {
                    return this.parseTupleType(isvalue);
                }
                else {
                    return this.parseRecordType(isvalue);
                }
            }
            case "fn":
            case "recursive?":
            case "recursive":
                return this.parsePCodeType();
            case "(": {
                this.ensureAndConsumeToken("(");
                const ptype = this.parseTypeSignature(literalTypeOk);
                this.ensureAndConsumeToken(")");

                return ptype;
            }
            default: {
                if(!literalTypeOk) {
                    this.raiseError(this.getCurrentLine(), "Unknown type option");
                }

                return this.parseLiteralType();
            }
        }
    }

    private parseTemplateTypeReference(): TypeSignature {
        return new TemplateTypeSignature(this.consumeTokenAndGetValue());
    }

    private parseTermList(): TypeSignature[] {
        let terms: TypeSignature[] = [];
        if (this.testToken("<")) {
            try {
                this.setRecover(this.scanMatchingParens("<", ">"));
                terms = this.parseListOf<TypeSignature>("<", ">", ",", () => {
                    return this.parseTypeSignature(true);
                })[0];

                this.clearRecover();
            }
            catch (ex) {
                this.processRecover();
            }
        }
        return terms;
    }

    private parseNominalType(): TypeSignature {
        const line = this.getCurrentLine();

        let ns: string | undefined = undefined;
        if (this.testToken(TokenStrings.Namespace)) {
            ns = this.consumeTokenAndGetValue();
            this.ensureAndConsumeToken("::");
        }

        const tname = this.consumeTokenAndGetValue();
        ns = this.m_penv.tryResolveNamespace(ns, tname);
        if (ns === undefined) {
            this.raiseError(line, "Could not resolve namespace");
        }

        let tnames: string[] = [tname];
        let terms: TypeSignature[] = this.parseTermList();

        while (!this.testFollows("::", TokenStrings.Type)) {
            this.ensureToken(TokenStrings.Type);
            const stname = this.consumeTokenAndGetValue();
            tnames.push(stname);

            const sterms = this.parseTermList();
            terms = [...terms, ...sterms];
        }

        return new NominalTypeSignature(ns as string, tnames, terms);
    }

    private parseLiteralType(): TypeSignature {
        this.consumeToken();
        this.ensureAndConsumeToken("(");
        
        let ttype: TypeSignature = this.m_penv.SpecialNoneSignature;
        let vv: boolean | number | string | undefined = undefined;
        if(this.testToken("true")) {
            this.consumeToken();
            ttype = this.m_penv.SpecialBoolSignature;
            vv = true;
        }
        else if(this.testToken("false")) {
            this.consumeToken();
            ttype = this.m_penv.SpecialBoolSignature;
            vv = false;
        }
        else if (this.testToken(TokenStrings.Int)) {
            ttype = this.m_penv.SpecialIntSignature;
            vv = this.consumeTokenAndGetValue();
        }
        else if (this.testToken(TokenStrings.Int)) {
            ttype = this.m_penv.SpecialNatSignature;
            vv = this.consumeTokenAndGetValue();
        }
        else {
            ttype = this.parseTypeSignature(false);
            this.ensureAndConsumeToken("::");

            this.ensureToken(TokenStrings.Identifier);
            const ename = this.consumeTokenAndGetValue();

            vv = ename;
        }

        return new LiteralTypeSignature(ttype, vv);
    }

    private parseTupleType(isvalue: boolean): TypeSignature {
        const line = this.getCurrentLine();
        let entries: [TypeSignature, boolean][] = [];

        try {
            this.setRecover(this.scanMatchingParens("[", "]"));
            entries = this.parseListOf<[TypeSignature, boolean]>("[", "]", ",", () => {
                const isopt = this.testAndConsumeTokenIf("?");
                if (isopt) {
                    this.ensureAndConsumeToken(":");
                }

                const rtype = this.parseTypeSignature(false);

                return [rtype, isopt];
            })[0];

            const firstOpt = entries.findIndex((entry) => entry[1]);
            if (entries.slice(firstOpt).findIndex((entry) => !entry[0]) !== -1) {
                this.raiseError(line, "Optional entries must all come at end of tuple");
            }

            this.clearRecover();
            return new TupleTypeSignature(isvalue, entries);
        }
        catch (ex) {
            this.processRecover();
            return new ParseErrorTypeSignature();
        }
    }

    private parseRecordType(isvalue: boolean): TypeSignature {
        let entries: [string, TypeSignature, boolean][] = [];

        try {
            this.setRecover(this.scanMatchingParens("{", "}"));

            let pnames = new Set<string>();
            entries = this.parseListOf<[string, TypeSignature, boolean]>("{", "}", ",", () => {
                this.ensureToken(TokenStrings.Identifier);

                const name = this.consumeTokenAndGetValue();
                if(UnsafeFieldNames.includes(name)) {
                    this.raiseError(this.getCurrentLine(), `Property name "${name}" is ambigious with the methods that Record may provide`);
                }

                if(pnames.has(name)) {
                    this.raiseError(this.getCurrentLine(), `Duplicate property name "${name}" in record declaration`);
                }
                pnames.add(name);

                const isopt = this.testAndConsumeTokenIf("?");
                this.ensureAndConsumeToken(":");
                const rtype = this.parseTypeSignature(false);

                return [name, rtype, isopt];
            })[0];

            this.clearRecover();
            return new RecordTypeSignature(isvalue, entries);
        }
        catch (ex) {
            this.processRecover();
            return new ParseErrorTypeSignature();
        }
    }

    private parsePCodeType(): TypeSignature {
        let recursive: "yes" | "no" | "cond" = "no";
        if (this.testAndConsumeTokenIf("recursive?")) {
            recursive = "cond";
        }
        if (this.testAndConsumeTokenIf("recursive")) {
            recursive = "yes";
        }

        this.ensureAndConsumeToken("fn");

        try {
            this.setRecover(this.scanMatchingParens("(", ")"));

            let fparams: FunctionParameter[] = [];
            let restName: string | undefined = undefined;
            let restType: TypeSignature | undefined = undefined;

            const params = this.parseListOf<[string, TypeSignature, boolean, boolean, boolean]>("(", ")", ",", () => {
                const isrest = this.testAndConsumeTokenIf("...");
                const isref = this.testAndConsumeTokenIf("ref");

                this.ensureToken(TokenStrings.Identifier);
                const pname = this.consumeTokenAndGetValue();
                const isopt = this.testAndConsumeTokenIf("?");
               
                this.ensureAndConsumeToken(":");
                const argtype = this.parseTypeSignature(false);

                if (isref && (isopt || isrest)) {
                    this.raiseError(this.getCurrentLine(), "Cannot use ref/borrow parameters here");
                }

                return [pname, argtype, isopt, isrest, isref];
            })[0];

            for (let i = 0; i < params.length; i++) {
                if (!params[i][3]) {
                    fparams.push(new FunctionParameter(params[i][0], params[i][1], params[i][2], params[i][4], false, undefined));
                }
                else {
                    if (i + 1 !== params.length) {
                        this.raiseError(this.getCurrentLine(), "Rest parameter must be last in parameter list");
                    }

                    restName = params[i][0];
                    restType = params[i][1];
                }
            }

            if (restName !== undefined && params.some((p) => p[2])) {
                this.raiseError(this.getCurrentLine(), "Cannot have optional and rest parameters in a function type");
            }

            this.ensureAndConsumeToken("->");
            const resultInfo = this.parseResultType(true);

            this.clearRecover();
            return new FunctionTypeSignature(recursive, fparams, restName, restType, resultInfo);
        }
        catch (ex) {
            this.processRecover();
            return new ParseErrorTypeSignature();
        }
    }

    private static orOfTypeSignatures(t1: TypeSignature, t2: TypeSignature): TypeSignature {
        const types = [
            ...((t1 instanceof UnionTypeSignature) ? t1.types : [t1]),
            ...((t2 instanceof UnionTypeSignature) ? t2.types : [t2]),
        ];

        return new UnionTypeSignature(types);
    }

    private andOfTypeSignatures(t1: TypeSignature, t2: TypeSignature): TypeSignature {
        if(t1 instanceof PlusTypeSignature || t2 instanceof PlusTypeSignature) {
            this.raiseError(this.getCurrentLine(), "Cannot mix & and + type combiners");
        }

        const types = [
            ...((t1 instanceof AndTypeSignature) ? t1.types : [t1]),
            ...((t2 instanceof AndTypeSignature) ? t2.types : [t2]),
        ];

        return new AndTypeSignature(types);
    }

    private plusOfTypeSignatures(t1: TypeSignature, t2: TypeSignature): TypeSignature {
        if(t1 instanceof AndTypeSignature || t2 instanceof AndTypeSignature) {
            this.raiseError(this.getCurrentLine(), "Cannot mix & and + type combiners");
        }

        const types = [
            ...((t1 instanceof PlusTypeSignature) ? t1.types : [t1]),
            ...((t2 instanceof PlusTypeSignature) ? t2.types : [t2]),
        ];

        return new PlusTypeSignature(types);
    }

    ////
    //Expression parsing
    private parseArguments(lparen: string, rparen: string): Arguments {
        const argSrcInfo = this.getCurrentSrcInfo();

        let seenNames = new Set<string>();
        let args: InvokeArgument[] = [];

        try {
            this.setRecover(this.scanMatchingParens(lparen, rparen));

            this.ensureAndConsumeToken(lparen);
            while (!this.testAndConsumeTokenIf(rparen)) {
                const line = this.getCurrentLine();
                const isref = this.testAndConsumeTokenIf("ref");

                if (this.testFollows(TokenStrings.Identifier, "=")) {
                    const name = this.consumeTokenAndGetValue();
                    this.ensureAndConsumeToken("=");
                    const exp = this.parseExpression();

                    if (seenNames.has(name)) {
                        this.raiseError(line, "Cannot have duplicate named argument name");
                    }

                    if (name !== "_") {
                        seenNames.add(name);
                    }

                    args.push(new NamedArgument(isref, name, exp));
                }
                else {
                    const isSpread = this.testAndConsumeTokenIf("...");
                    const exp = this.parseExpression();

                    args.push(new PositionalArgument(isref, isSpread, exp));
                }

                if (this.testAndConsumeTokenIf(",")) {
                    this.ensureNotToken(rparen);
                }
                else {
                    this.ensureToken(rparen);
                }
            }

            this.clearRecover();
            return new Arguments(args);
        }
        catch (ex) {
            this.processRecover();
            return new Arguments([new PositionalArgument(false, false, new InvalidExpression(argSrcInfo))]);
        }
    }

    private parseTemplateArguments(): TemplateArguments {
        try {
            this.setRecover(this.scanMatchingParens("<", ">"));
            let targs: TypeSignature[] = [];

            this.ensureAndConsumeToken("<");
            while (!this.testAndConsumeTokenIf(">")) {
                targs.push(this.parseTypeSignature(true));

                if (this.testAndConsumeTokenIf(",")) {
                    this.ensureNotToken(">");
                }
                else {
                    this.ensureToken(">");
                }
            }

            this.clearRecover();
            return new TemplateArguments(targs);
        }
        catch (ex) {
            this.processRecover();
            return new TemplateArguments([]);
        }
    }

    private parsePragmaArguments(): PragmaArguments {
        try {
            this.setRecover(this.scanMatchingParens("[", "]"));
            let pargs: [TypeSignature, string][] = [];

            let recursive: "yes" | "no" | "cond" = "no";
            this.ensureAndConsumeToken("[");
            while (!this.testAndConsumeTokenIf("]")) {
                if (this.testToken("recursive") || this.testToken("recursive?")) {
                    if (recursive !== "no") {
                        this.raiseError(this.getCurrentLine(), "Multiple recursive pragmas on call");
                    }

                    recursive = this.testToken("recursive") ? "yes" : "cond";
                    this.consumeToken();
                }
                else {
                    const ptype = this.parseTypeSignature(false);
                    const pstr = this.testToken(TokenStrings.TypedString) ? this.consumeTokenAndGetValue() : "";

                    pargs.push([ptype, pstr]);
                }

                if (this.testAndConsumeTokenIf(",")) {
                    this.ensureNotToken("]");
                }
                else {
                    this.ensureToken("]");
                }
            }

            this.clearRecover();
            return new PragmaArguments(recursive, pargs);
        }
        catch (ex) {
            this.processRecover();
            return new PragmaArguments("no", []);
        }
    }

    private parseConstructorPrimary(otype: TypeSignature): Expression {
        const sinfo = this.getCurrentSrcInfo();

        if(!this.testToken("@") && !this.testToken("#")) {
            this.raiseError(sinfo.line, "Expected either @ or #");
        }

        const isvalue = this.testToken("#");
        this.consumeToken();

        const args = this.parseArguments("{", "}");

        return new ConstructorPrimaryExpression(sinfo, isvalue, otype, args);
    }

    private parseConstructorPrimaryWithFactory(otype: TypeSignature): Expression {
        const sinfo = this.getCurrentSrcInfo();

        if(!this.testToken("@") && !this.testToken("#")) {
            this.raiseError(sinfo.line, "Expected either @ or #");
        }

        const isvalue = this.testToken("#");
        this.consumeToken();
        this.ensureToken(TokenStrings.Identifier);

        const fname = this.consumeTokenAndGetValue();
        const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
        const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new PragmaArguments("no", []);
        const args = this.parseArguments("(", ")");

        return new ConstructorPrimaryWithFactoryExpression(sinfo, isvalue, otype, fname, pragmas, targs, args);
    }

    private parsePCodeTerm(): Expression {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();

        const isrecursive = this.testAndConsumeTokenIf("recursive");

        this.ensureAndConsumeToken("fn");
        const sig = this.parseInvokableCommon(InvokableKind.PCode, false, [], isrecursive ? "yes" : "no", [], [], undefined);
        const someAuto = sig.params.some((param) => param.type instanceof AutoTypeSignature) || (sig.optRestType !== undefined && sig.optRestType instanceof AutoTypeSignature) || (sig.resultType instanceof AutoTypeSignature);
        const allAuto = sig.params.every((param) => param.type instanceof AutoTypeSignature) && (sig.optRestType === undefined || sig.optRestType instanceof AutoTypeSignature) && (sig.resultType instanceof AutoTypeSignature);
        if (someAuto && !allAuto) {
            this.raiseError(line, "Cannot have mixed of auto propagated and explicit types on lambda arguments/return");
        }

        sig.captureSet.forEach((v) => {
            this.m_penv.getCurrentFunctionScope().useLocalVar(v);
        });

        return new ConstructorPCodeExpression(sinfo, allAuto, sig);
    }

    private parseFollowType(): TypeSignature {
        if(this.testToken(TokenStrings.Template)) {
            return this.parseTemplateTypeReference();
        }
        else {
            const line = this.getCurrentLine();

            let ns: string | undefined = undefined;
            if (this.testToken(TokenStrings.Namespace)) {
                ns = this.consumeTokenAndGetValue();
                this.ensureAndConsumeToken("::");
            }

            const tname = this.consumeTokenAndGetValue();
            ns = this.m_penv.tryResolveNamespace(ns, tname);
            if (ns === undefined) {
                this.raiseError(line, "Could not resolve namespace");
            }

            let tnames: string[] = [tname];
            let terms: TypeSignature[] = [];

            //
            //TODO: follow types -- used for stringof, datastring, and unit types cannot be template types
            //      maybe this is ok but we might want to allow it (at least for stringof/datastring)
            //

            return new NominalTypeSignature(ns as string, tnames, terms);
        }
    }

    private tryParseFollowConsType(): [boolean, TypeSignature] {
        if(!this.testToken("#") && !this.testToken("@")) {
            return [true, this.m_penv.SpecialNoneSignature]; 
        }
        else {
            this.ensureAndConsumeToken("#");
            const ttype = this.parseFollowType();

            return [false, ttype];
        }
    }

    private parsePrimaryExpression(): Expression {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();

        const tk = this.peekToken();
        if (tk === "none") {
            this.consumeToken();
            return new LiteralNoneExpression(sinfo);
        }
        else if (tk === "true" || tk === "false") {
            this.consumeToken();
            return new LiteralBoolExpression(sinfo, tk === "true");
        }
        else if (tk === TokenStrings.Int) {
            const istr = this.consumeTokenAndGetValue();
            const [islit, ttype] = this.tryParseFollowConsType();

            return islit ? new LiteralIntegerExpression(sinfo, istr) : new LiteralTypedNumericConstructorExpression(sinfo, istr, this.m_penv.SpecialIntSignature, ttype);
        }
        else if (tk === TokenStrings.Nat) {
            const istr = this.consumeTokenAndGetValue();
            const [islit, ttype] = this.tryParseFollowConsType();

            return islit ? new LiteralNaturalExpression(sinfo, istr) : new LiteralTypedNumericConstructorExpression(sinfo, istr, this.m_penv.SpecialNatSignature, ttype);
        }
        else if (tk === TokenStrings.Float) {
            const fstr = this.consumeTokenAndGetValue();
            const [islit, ttype] = this.tryParseFollowConsType();

            return islit ? new LiteralFloatExpression(sinfo, fstr) : new LiteralTypedNumericConstructorExpression(sinfo, fstr, this.m_penv.SpecialFloatSignature, ttype);
        }
        else if (tk === TokenStrings.Decimal) {
            const fstr = this.consumeTokenAndGetValue();
            const [islit, ttype] = this.tryParseFollowConsType();

            return islit ? new LiteralDecimalExpression(sinfo, fstr) : new LiteralTypedNumericConstructorExpression(sinfo, fstr, this.m_penv.SpecialDecimalSignature, ttype);
        }
        else if (tk === TokenStrings.BigInt) {
            const istr = this.consumeTokenAndGetValue();
            const [islit, ttype] = this.tryParseFollowConsType();

            return islit ? new LiteralBigIntegerExpression(sinfo, istr) : new LiteralTypedNumericConstructorExpression(sinfo, istr, this.m_penv.SpecialBigIntSignature, ttype);
        }
        else if (tk === TokenStrings.BigNat) {
            const istr = this.consumeTokenAndGetValue();
            const [islit, ttype] = this.tryParseFollowConsType();

            return islit ? new LiteralBigNaturalExpression(sinfo, istr) : new LiteralTypedNumericConstructorExpression(sinfo, istr, this.m_penv.SpecialBigNatSignature, ttype);
        }
        else if (tk === TokenStrings.Rational) {
            const istr = this.consumeTokenAndGetValue();
            const [islit, ttype] = this.tryParseFollowConsType();

            return islit ? new LiteralRationalExpression(sinfo, istr) : new LiteralTypedNumericConstructorExpression(sinfo, istr, this.m_penv.SpecialRationalSignature, ttype);
        }
        else if (tk === TokenStrings.String) {
            const sstr = this.consumeTokenAndGetValue(); //keep in escaped format
            return new LiteralStringExpression(sinfo, sstr);
        }
        else if (tk == TokenStrings.TypedString) {
            const sstr = this.consumeTokenAndGetValue(); //keep in escaped format

            if (this.testToken("#") || this.testToken("@")) {
                const isvalue = this.testToken("#");
                this.consumeToken();
                const ttype = this.parseFollowType();
                
                return new LiteralTypedStringConstructorExpression(sinfo, isvalue, sstr, ttype);
            }
            else {
                const ttype = this.parseFollowType();
                
                return new LiteralTypedStringExpression(sinfo, sstr, ttype);
            }
        }
        else if (tk === TokenStrings.Regex) {
            const restr = this.consumeTokenAndGetValue(); //keep in escaped format
            const re = BSQRegex.parse(restr);
            if(typeof(re) === "string") {
                this.raiseError(line, re);
            }

            this.m_penv.assembly.addLiteralRegex(re as BSQRegex);
            return new LiteralRegexExpression(sinfo, re as BSQRegex);
        }
        else if (tk === "ok" || tk === "err") {
            this.consumeToken();
            this.ensureAndConsumeToken("(");
            const arg = this.parseExpression();
            this.ensureAndConsumeToken(")");

            return new SpecialConstructorExpression(sinfo, this.m_penv.getCurrentFunctionScope().getReturnType(), tk, arg);
        }
        else if (tk === TokenStrings.Identifier) {
            let istr = this.consumeTokenAndGetValue();

            const isvar = this.m_penv.isVarDefinedInAnyScope(istr);
            if (isvar) {
                //In lambda/pcode bodies we want to bind "this" to the enclosing this *NOT* the accidental "this" any internal method invocations
                if (this.m_penv.getCurrentFunctionScope().isPCodeEnv() && istr === "this") {
                    istr = "%this_captured";
                }

                this.m_penv.getCurrentFunctionScope().useLocalVar(istr);

                if (this.testToken("[")) {
                    const pragmas = this.parsePragmaArguments();
                    const args = this.parseArguments("(", ")");
                    return new PCodeInvokeExpression(sinfo, istr, pragmas, args);
                }
                else if (this.testToken("(")) {
                    const args = this.parseArguments("(", ")");
                    return new PCodeInvokeExpression(sinfo, istr, new PragmaArguments("no", []), args);
                }
                else {
                    return new AccessVariableExpression(sinfo, istr);
                }
            }
            else {
                const ns = this.m_penv.tryResolveNamespace(undefined, istr);
                if (ns === undefined) {
                    this.raiseError(line, "Cannot resolve namespace for invoke");
                }

                const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
                const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new PragmaArguments("no", []);
                const args = this.parseArguments("(", ")");

                return new CallNamespaceFunctionOrOperatorExpression(sinfo, ns as string, istr, targs, pragmas, args);
            }
        }
        else if (tk === TokenStrings.Operator) {
            const istr = this.consumeTokenAndGetValue();
            const ns = this.m_penv.tryResolveNamespace(undefined, istr);
            if (ns === undefined) {
                this.raiseError(line, "Cannot resolve namespace for invoke");
            }

            const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new PragmaArguments("no", []);
            const args = this.parseArguments("(", ")");

            return new CallNamespaceFunctionOrOperatorExpression(sinfo, ns as string, istr, new TemplateArguments([]), pragmas, args);
        }
        else if (tk === "fn" || this.testFollows("recursive", "fn")) {
            return this.parsePCodeTerm();
        }
        else if (tk === "(") {
            try {
                this.setRecover(this.scanMatchingParens("(", ")"));

                this.consumeToken();
                const exp = this.parseExpression();
                this.ensureAndConsumeToken(")");

                this.clearRecover();
                return exp;
            }
            catch (ex) {
                this.processRecover();
                return new InvalidExpression(sinfo);
            }
        }
        else if (this.testToken("#") || this.testToken("@")) {
            const isvalue = this.testToken("#");
            this.consumeToken();

            if (this.testToken("[")) {
                const args = this.parseArguments("[", "]");
                return new ConstructorTupleExpression(sinfo, isvalue, args);
            }
            else {
                const args = this.parseArguments("{", "}");
                return new ConstructorRecordExpression(sinfo, isvalue, args);
            }
        }
        else if (this.testToken("(|")) {
            const args = this.parseArguments("(|", "|)");
            return new ConstructorEphemeralValueList(sinfo, args);
        }
        else if (this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Identifier)) {
            //it is a namespace access of some type
            const ns = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            if (!this.testToken("<") && !this.testToken("[") && !this.testToken("(")) {
                //just a constant access
                return new AccessNamespaceConstantExpression(sinfo, ns, name);
            }
            else {
                const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
                const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new PragmaArguments("no", []);
                const args = this.parseArguments("(", ")");

                return new CallNamespaceFunctionOrOperatorExpression(sinfo, ns, name, targs, pragmas, args);
            }
        }
        else if (this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Operator)) {
            //it is a namespace access of some type
            const ns = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new PragmaArguments("no", []);
            const args = this.parseArguments("(", ")");

            return new CallNamespaceFunctionOrOperatorExpression(sinfo, ns, name, new TemplateArguments([]), pragmas, args);
        }
        else {
            const ttype = this.parseTypeSignature(false);
            if (this.testFollows("::", TokenStrings.Identifier)) {
                this.consumeToken();
                const name = this.consumeTokenAndGetValue();
                if (!this.testToken("<") && !this.testToken("[") && !this.testToken("(")) {
                    //just a static access
                    return new AccessStaticFieldExpression(sinfo, ttype, name);
                }
                else {
                    const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
                    const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new PragmaArguments("no", []);
                    const args = this.parseArguments("(", ")");

                    return new CallStaticFunctionOrOperatorExpression(sinfo, ttype, name, targs, pragmas, args);
                }
            }
            else if (this.testFollows("@", TokenStrings.Identifier) || this.testFollows("#", TokenStrings.Identifier)) {
                return this.parseConstructorPrimaryWithFactory(ttype);
            }
            else if (this.testFollows("@", "{") || this.testFollows("#", "{")) {
                return this.parseConstructorPrimary(ttype);
            }
            else if (ttype instanceof TemplateTypeSignature) {
                return new LiteralParamerterValueExpression(sinfo, ttype);
            }
            else {
                this.raiseError(line, "Unknown token sequence in parsing expression");
                return new InvalidExpression(sinfo);
            }
        }
    }
    
    private handleSpecialCaseMethods(sinfo: SourceInfo, isElvis: boolean, specificResolve: TypeSignature | undefined, name: string): PostfixOperation {
        if (specificResolve !== undefined) {
            this.raiseError(this.getCurrentLine(), "Cannot use specific resolve on special methods");
        }

        const line = sinfo.line;
        if (name === "is") {
            this.ensureAndConsumeToken("<");
            const istype = this.parseTypeSignature(true);
            this.ensureAndConsumeToken(">");
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");

            return new PostfixIs(sinfo, isElvis, istype);
        }
        else if (name === "isSome") {
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");

            return new PostfixIs(sinfo, isElvis, this.m_penv.SpecialSomeSignature);
        }
        else if (name === "isNone") {
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");

            return new PostfixIs(sinfo, isElvis, this.m_penv.SpecialNoneSignature);
        }
        else if (name === "as") {
            this.ensureAndConsumeToken("<");
            const astype = this.parseTypeSignature(true);
            this.ensureAndConsumeToken(">");
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");

            return new PostfixAs(sinfo, isElvis, astype);
        }
        else if (name === "update") {
            const isBinder = this.testAndConsumeTokenIf("$")
            if (this.testFollows("(", TokenStrings.Int)) {
                const updates = this.parseListOf<{ index: number, value: Expression }>("(", ")", ",", () => {
                    this.ensureToken(TokenStrings.Int);
                    const idx = Number.parseInt(this.consumeTokenAndGetValue());
                    this.ensureAndConsumeToken("=");
                    const value = this.parseExpression();

                    return { index: idx, value: value };
                })[0].sort((a, b) => a.index - b.index);

                return new PostfixModifyWithIndecies(sinfo, isElvis, isBinder, updates);
            }
            else if (this.testFollows("(", TokenStrings.Identifier)) {
                const updates = this.parseListOf<{ name: string, value: Expression }>("(", ")", ",", () => {
                    this.ensureToken(TokenStrings.Identifier);
                    const uname = this.consumeTokenAndGetValue();
                    this.ensureAndConsumeToken("=");
                    const value = this.parseExpression();

                    return { name: uname, value: value };
                })[0].sort((a, b) => a.name.localeCompare(b.name));

                return new PostfixModifyWithNames(sinfo, isElvis, isBinder, updates);
            }
            else {
                this.raiseError(line, "Expected list of property/field or tuple updates");
                return (undefined as unknown) as PostfixOperation;
            }
        }
        else if (name === "hasIndex") {
            this.ensureAndConsumeToken("(");
            this.ensureToken(TokenStrings.Int);
            const idx = Number.parseInt(this.consumeTokenAndGetValue()); 
            this.ensureAndConsumeToken(")");
            return new PostfixHasIndex(sinfo, isElvis, idx);
        }
        else if (name === "hasProperty") {
            this.ensureAndConsumeToken("(");
            this.ensureToken(TokenStrings.Identifier);
            const pname = this.consumeTokenAndGetValue(); 
            this.ensureAndConsumeToken(")");
            return new PostfixHasProperty(sinfo, isElvis, pname);
        }
        else {
            this.raiseError(line, "unknown special operation");
            return (undefined as unknown) as PostfixOperation;
        }
    }

    private parsePostfixExpression(): Expression {
        const rootinfo = this.getCurrentSrcInfo();
        let rootexp = this.parsePrimaryExpression();

        let ops: PostfixOperation[] = [];
        while (true) {
            const sinfo = this.getCurrentSrcInfo();

            const tk = this.peekToken();
            if (tk === "." || tk === "?.") {
                const isElvis = tk === "?.";

                this.consumeToken();
                if (this.testToken(TokenStrings.Int)) {
                    const index = Number.parseInt(this.consumeTokenAndGetValue());
                    ops.push(new PostfixAccessFromIndex(sinfo, isElvis, index));
                }
                else if (this.testFollows("#", "[") || this.testFollows("@", "[")) {
                    const isvalue = this.testToken("#");
                    this.consumeToken();

                    const indecies = this.parseListOf<{ index: number, reqtype: TypeSignature | undefined }>("[", "]", ",", () => {
                        this.ensureToken(TokenStrings.Int);
                        const idx = Number.parseInt(this.consumeTokenAndGetValue());

                        if (!this.testAndConsumeTokenIf(":")) {
                            return { index: idx, reqtype: undefined };
                        }
                        else {
                            return { index: idx, reqtype: this.parseTypeSignature(false) };
                        }
                    })[0];

                    if(indecies.length === 0) {
                        this.raiseError(sinfo.line, "You must have at least one index when projecting");
                    }

                    ops.push(new PostfixProjectFromIndecies(sinfo, isElvis, isvalue, false, indecies));
                }
                else if (this.testFollows("#", "{") || this.testFollows("@", "{")) {
                    const isvalue = this.testToken("#");
                    this.consumeToken();

                    const names = this.parseListOf<{ name: string, reqtype: TypeSignature | undefined }>("{", "}", ",", () => {
                        this.ensureToken(TokenStrings.Identifier);
                        const nn = this.consumeTokenAndGetValue();

                        if (!this.testAndConsumeTokenIf(":")) {
                            return { name: nn, reqtype: undefined };
                        }
                        else {
                            return { name: nn, reqtype: this.parseTypeSignature(false) };
                        }
                    })[0];

                    if(names.length === 0) {
                        this.raiseError(sinfo.line, "You must have at least one name when projecting");
                    }

                    ops.push(new PostfixProjectFromNames(sinfo, isElvis, isvalue, false, names));
                }
                else if(this.testToken("(|")) {
                    if (this.testFollows("(|", TokenStrings.Int)) {
                        const indecies = this.parseListOf<{ index: number, reqtype: TypeSignature | undefined }>("(|", "|)", ",", () => {
                            this.ensureToken(TokenStrings.Int);
                            const idx = Number.parseInt(this.consumeTokenAndGetValue());
                            
                            if (!this.testAndConsumeTokenIf(":")) {
                                return { index: idx, reqtype: undefined};
                            }
                            else {
                                return { index: idx, reqtype: this.parseTypeSignature(false) };
                            }
                        })[0];

                        if (indecies.length <= 1) {
                            this.raiseError(sinfo.line, "You must have at least two indecies when projecting out a Ephemeral value pack (otherwise just access the index directly)");
                        }

                        ops.push(new PostfixProjectFromIndecies(sinfo, isElvis, false, true, indecies));
                    }
                    else {
                        const names = this.parseListOf<{ name: string, isopt: boolean, reqtype: TypeSignature | undefined }>("(|", "|)", ",", () => {
                            this.ensureToken(TokenStrings.Identifier);
                            const nn = this.consumeTokenAndGetValue();
                            if(this.testAndConsumeTokenIf("?")) {
                                this.raiseError(sinfo.line, "Cannot have optional part in Ephemeral List projection");
                            }

                            if (!this.testAndConsumeTokenIf(":")) {
                                return { name: nn, isopt: false, reqtype: undefined };
                            }
                            else {
                                return { name: nn, isopt: false, reqtype: this.parseTypeSignature(false) };
                            }
                        })[0];

                        if (names.length <= 1) {
                            this.raiseError(sinfo.line, "You must have at least two names when projecting out a Ephemeral value pack (otherwise just access the property/field directly)");
                        }

                        ops.push(new PostfixProjectFromNames(sinfo, isElvis, false, true, names));
                    }
                }
                else {
                    let specificResolve: TypeSignature | undefined = undefined;
                    if (this.testToken(TokenStrings.Namespace) || this.testToken(TokenStrings.Type) || this.testToken(TokenStrings.Template)) {
                        specificResolve = this.parseTypeSignature(false);
                        this.ensureAndConsumeToken("::");
                    }

                    this.ensureToken(TokenStrings.Identifier);
                    const name = this.consumeTokenAndGetValue();

                    if (name === "as" || name === "is" || name === "isSome" || name === "isNone" || name === "update" || name === "hasIndex" || name === "hasProperty") {
                        ops.push(this.handleSpecialCaseMethods(sinfo, isElvis, specificResolve, name));
                    }
                    else if (!(this.testToken("<") || this.testToken("[") || this.testToken("("))) {
                        if (specificResolve !== undefined) {
                            this.raiseError(this.getCurrentLine(), "Encountered named access but given type resolver (only valid on method calls)");
                        }

                        ops.push(new PostfixAccessFromName(sinfo, isElvis, name));
                    }
                    else {
                        //ugly ambiguity with < -- the follows should be a NS, Type, or T token
                        //    this.f.g < (1 + 2) and this.f.g<(Int)>() don't know with bounded lookahead :(
                        //
                        //TODO: in theory it could also be a "(" and we need to do a tryParseType thing
                        //
                        if (this.testToken("<")) {
                            if (this.testFollows("<", TokenStrings.Namespace) || this.testFollows("<", TokenStrings.Type) || this.testFollows("<", TokenStrings.Template)) {
                                const terms = this.parseTemplateArguments();
                                const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new PragmaArguments("no", []);
                                const args = this.parseArguments("(", ")");

                                ops.push(new PostfixInvoke(sinfo, isElvis, specificResolve, name, terms, pragmas, args));
                            }
                            else {
                                if (specificResolve !== undefined) {
                                    this.raiseError(this.getCurrentLine(), "Encountered named access but given type resolver (only valid on method calls)");
                                }

                                ops.push(new PostfixAccessFromName(sinfo, isElvis, name));
                            }
                        }
                        else {
                            const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new PragmaArguments("no", []);

                            //
                            //TODO add binder support here later -- x.f<Int>${g, h}($g + 1, $h - 5)
                            //
                            const args = this.parseArguments("(", ")");

                            ops.push(new PostfixInvoke(sinfo, isElvis, specificResolve, name, new TemplateArguments([]), pragmas, args));
                        }
                    }
                }
            }
            else {
                if (ops.length === 0) {
                    return rootexp;
                }
                else {
                    return new PostfixOp(rootinfo, rootexp, ops);
                }
            }
        }
    }

    private parseStatementExpression(): Expression {
        if (this.testToken("{|")) {
            return this.parseBlockStatementExpression();
        }
        else if (this.testToken("if")) {
            return this.parseIfExpression();
        }
        else if (this.testToken("switch")) {
            return this.parseMatchExpression();
        }
        else {
            return this.parsePostfixExpression();
        }
    }

    private parsePrefixExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        if (this.testToken("!")) {
            const op = this.consumeTokenAndGetValue();
            return new PrefixNotOp(sinfo, op, this.parsePrefixExpression());
        }
        else if(this.testToken("+") || this.testToken("-") || this.testToken(TokenStrings.Operator)) {
            const ons = this.m_penv.tryResolveAsPrefixUnaryOperator(this.peekTokenData(), 1);
            if(ons === undefined) {
                this.raiseError(sinfo.line, "Could not resolve operator");
            }

            const op = this.consumeTokenAndGetValue();
            const arg = new PositionalArgument(false, false, this.parsePrefixExpression());
            return new CallNamespaceFunctionOrOperatorExpression(sinfo, ons as string, op, new TemplateArguments([]), new PragmaArguments("no", []), new Arguments([arg]));
        }
        else {
            return this.parseStatementExpression();
        }
    }

    private parseMultiplicativeExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parsePrefixExpression();

        if(this.testToken("*") || this.testToken("/") || this.testToken(TokenStrings.Operator)) {
            const ons = this.m_penv.tryResolveAsInfixBinaryOperator(this.peekTokenData(), 2);
            if(ons === undefined) {
                this.raiseError(sinfo.line, "Could not resolve operator");
            }

            const op = this.consumeTokenAndGetValue();
            const lhs = new PositionalArgument(false, false, exp);
            const rhs = new PositionalArgument(false, false, this.parseMultiplicativeExpression());
            return new CallNamespaceFunctionOrOperatorExpression(sinfo, ons as string, op, new TemplateArguments([]), new PragmaArguments("no", []), new Arguments([lhs, rhs]));
        }
        else {
            return exp;
        }
    }

    private parseAdditiveExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseMultiplicativeExpression();

        if(this.testToken("+") || this.testToken("-") || this.testToken(TokenStrings.Operator)) {
            const ons = this.m_penv.tryResolveAsInfixBinaryOperator(this.peekTokenData(), 3);
            if (ons === undefined) {
                this.raiseError(sinfo.line, "Could not resolve operator");
            }

            const op = this.consumeTokenAndGetValue();
            const lhs = new PositionalArgument(false, false, exp);
            const rhs = new PositionalArgument(false, false, this.parseAdditiveExpression());
            return new CallNamespaceFunctionOrOperatorExpression(sinfo, ons as string, op, new TemplateArguments([]), new PragmaArguments("no", []), new Arguments([lhs, rhs]));
        }
        else {
            return exp;
        }
    }

    private parseRelationalExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseAdditiveExpression();

        if (this.testToken("==") || this.testToken("!=")) {
            const op = this.consumeTokenAndGetValue();
            return new BinEqExpression(sinfo, exp, op, this.parseRelationalExpression());
        }
        else if (this.testToken("<") || this.testToken(">") || this.testToken("<=") || this.testToken(">=")) {
            const op = this.consumeTokenAndGetValue();
            return new BinCmpExpression(sinfo, exp, op, this.parseRelationalExpression());
        }
        else if(this.testToken(TokenStrings.Operator)) {
            const ons = this.m_penv.tryResolveAsInfixBinaryOperator(this.peekTokenData(), 4);
            if (ons === undefined) {
                this.raiseError(sinfo.line, "Could not resolve operator");
            }

            const op = this.consumeTokenAndGetValue();
            const lhs = new PositionalArgument(false, false, exp);
            const rhs = new PositionalArgument(false, false, this.parseRelationalExpression());
            return new CallNamespaceFunctionOrOperatorExpression(sinfo, ons as string, op, new TemplateArguments([]), new PragmaArguments("no", []), new Arguments([lhs, rhs]));
        }
        else {
            return exp;
        }
    }

    private parseNonecheckExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseRelationalExpression();

        if (this.testAndConsumeTokenIf("?&")) {
            return new NonecheckExpression(sinfo, exp, this.parseNonecheckExpression());
        }
        else {
            return exp;
        }
    }

    private parseCoalesceExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseNonecheckExpression();

        if (this.testAndConsumeTokenIf("?|")) {
            return new CoalesceExpression(sinfo, exp, this.parseCoalesceExpression());
        }
        else {
            return exp;
        }
    }

    private parseImpliesExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseCoalesceExpression();

        if (this.testAndConsumeTokenIf("==>")) {
            return new BinLogicExpression(sinfo, exp, "==>", this.parseImpliesExpression());
        }
        else {
            return exp;
        }
    }

    private parseAndExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseImpliesExpression();

        if (this.testAndConsumeTokenIf("&&")) {
            return new BinLogicExpression(sinfo, exp, "&&", this.parseAndExpression());
        }
        else {
            return exp;
        }
    }

    private parseOrExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseAndExpression();

        if (this.testAndConsumeTokenIf("||")) {
            return new BinLogicExpression(sinfo, exp, "||", this.parseOrExpression());
        }
        else {
            return exp;
        }
    }

    private parseMapEntryConstructorExpression(disallowMapEntry?: boolean): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseOrExpression();

        if (!(disallowMapEntry) && this.testAndConsumeTokenIf("=>")) {
            return new MapEntryConstructorExpression(sinfo, exp, this.parseMapEntryConstructorExpression());
        }
        else {
            return exp;
        }
    }

    private parseSelectExpression(disallowMapEntry?: boolean): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const texp = this.parseMapEntryConstructorExpression(disallowMapEntry);

        if (this.testAndConsumeTokenIf("?")) {
            const exp1 = this.parseMapEntryConstructorExpression(disallowMapEntry);
            this.ensureAndConsumeToken(":");
            const exp2 = this.parseSelectExpression(disallowMapEntry);

            return new SelectExpression(sinfo, texp, exp1, exp2);
        }
        else {
            return texp;
        }
    }

    private parseExpOrExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const texp = this.parseSelectExpression();

        if (this.testAndConsumeTokenIf("or")) {
            if (!this.testToken("return") && !this.testToken("yield")) {
                this.raiseError(this.getCurrentLine(), "Expected 'return' or 'yield");
            }

            const action = this.consumeTokenAndGetValue();
            let value: undefined | Expression[] = undefined;
            let cond: undefined | Expression = undefined;

            if (!this.testToken(";")) {
                this.m_penv.getCurrentFunctionScope().pushLocalScope();
                this.m_penv.getCurrentFunctionScope().defineLocalVar("$value");
                this.m_penv.getCurrentFunctionScope().setImplicitValueState(true);

                try {
                    if (this.testToken("when")) {
                        this.consumeToken();
                        cond = this.parseExpression();
                    }
                    else {
                        value = this.parseEphemeralListOf(() => this.parseExpression());
                        if (this.testToken("when")) {
                            this.consumeToken();
                            cond = this.parseExpression();
                        }
                    }
                }
                finally {
                    this.m_penv.getCurrentFunctionScope().setImplicitValueState(false);
                    this.m_penv.popFunctionScope();
                }
            }

            return new ExpOrExpression(sinfo, texp, action, value, cond);
        }
        else {
            return texp;
        }
    }

    private parseBlockStatementExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        this.m_penv.getCurrentFunctionScope().pushLocalScope();
        let stmts: Statement[] = [];
        try {
            this.setRecover(this.scanMatchingParens("{|", "|}"));

            this.consumeToken();
            while (!this.testAndConsumeTokenIf("|}")) {
                stmts.push(this.parseStatement());
            }

            this.m_penv.getCurrentFunctionScope().popLocalScope();

            this.clearRecover();
            return new BlockStatementExpression(sinfo, stmts);
        }
        catch (ex) {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
            this.processRecover();
            return new BlockStatementExpression(sinfo, [new InvalidStatement(sinfo)]);
        }
    }

    private parseIfExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        let conds: CondBranchEntry<Expression>[] = [];

        this.ensureAndConsumeToken("if");
        this.ensureAndConsumeToken("(");
        const iftest = this.parseExpression();
        this.ensureAndConsumeToken(")");

        const ifbody = this.parseExpression();
        conds.push(new CondBranchEntry<Expression>(iftest, ifbody));

        while (this.testAndConsumeTokenIf("elif")) {
            this.ensureAndConsumeToken("(");
            const eliftest = this.parseExpression();
            this.ensureAndConsumeToken(")");
            const elifbody = this.parseExpression();

            conds.push(new CondBranchEntry<Expression>(eliftest, elifbody));
        }

        this.ensureAndConsumeToken("else");
        const elsebody = this.parseExpression();

        return new IfExpression(sinfo, new IfElse<Expression>(conds, elsebody));
    }

    private parseMatchExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        this.ensureAndConsumeToken("switch");

        this.ensureAndConsumeToken("(");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(")");

        let entries: MatchEntry<Expression>[] = [];
        this.ensureAndConsumeToken("{");
        while (this.testToken("type") || this.testToken("case") || (this.testToken(TokenStrings.Identifier) && this.peekTokenData() === "_")) {
            if (this.testToken("type")) {
                entries.push(this.parseMatchEntry<Expression>(sinfo, "type", () => this.parseExpression()));
            }
            else {
                entries.push(this.parseMatchEntry<Expression>(sinfo, "case", () => this.parseExpression()));
            }
        }
        this.ensureAndConsumeToken("}");

        return new MatchExpression(sinfo, mexp, entries);
    }

    private parseExpression(): Expression {
        return this.parseExpOrExpression();
    }

    ////
    //Statement parsing

    parseStructuredAssignment(sinfo: SourceInfo, vars: "let" | "var" | undefined, trequired: boolean, literalok: boolean, decls: Set<string>): StructuredAssignment {
        if (this.testToken("#") || this.testToken("@")) {
            const isvalue = this.testToken("#");
            this.consumeToken();

            if (this.testToken("[")) {
                const assigns = this.parseListOf<StructuredAssignment>("[", "]", ",", () => {
                    return this.parseStructuredAssignment(this.getCurrentSrcInfo(), vars, trequired, literalok, decls);
                })[0];

                return new TupleStructuredAssignment(isvalue, assigns);
            }
            else {
                const assigns = this.parseListOf<[string, StructuredAssignment]>("{", "}", ",", () => {
                    this.ensureToken(TokenStrings.Identifier);
                    const name = this.consumeTokenAndGetValue();

                    this.ensureAndConsumeToken("=");
                    const subg = this.parseStructuredAssignment(this.getCurrentSrcInfo(), vars, trequired, literalok, decls);

                    return [name, subg];
                })[0];

                return new RecordStructuredAssignment(isvalue, assigns);
            }
        }
        else if (this.testToken("(|")) {
            const assigns = this.parseListOf<StructuredAssignment>("(|", "|)", ",", () => {
                return this.parseStructuredAssignment(this.getCurrentSrcInfo(), vars, trequired, literalok, decls);
            })[0];

            return new ValueListStructuredAssignment(assigns);
        }
        else if (this.testToken("none")) {
            if(!literalok) {
                this.raiseError(sinfo.line, "Literal match is not allowed");
            }

            this.consumeToken();
            return new ConstValueStructuredAssignment(new LiteralNoneExpression(sinfo));
        }
        else if (this.testToken("true") || this.testToken("false")) {
            if(!literalok) {
                this.raiseError(sinfo.line, "Literal match is not allowed");
            }

            const tk = this.consumeTokenAndGetValue();
            return new ConstValueStructuredAssignment(new LiteralBoolExpression(sinfo, tk === "true"));
        }
        else if (this.testToken(TokenStrings.Int) || this.testFollows("+", TokenStrings.Int) || this.testFollows("-", TokenStrings.Int)) {
            if(!literalok) {
                this.raiseError(sinfo.line, "Literal match is not allowed");
            }

            const isneg = this.testToken("-");
            if(this.testToken("-") || this.testToken("+")) {
                this.consumeToken();
            }
            const istr = (isneg ? "-" : "") + this.consumeTokenAndGetValue();
            const [islit, ttype] = this.tryParseFollowConsType();

            return new ConstValueStructuredAssignment(islit ? new LiteralIntegerExpression(sinfo, istr) : new LiteralTypedNumericConstructorExpression(sinfo, istr, this.m_penv.SpecialIntSignature, ttype));
        }
        else if (this.testToken(TokenStrings.Nat) || this.testFollows("+", TokenStrings.Nat)) {
            if(!literalok) {
                this.raiseError(sinfo.line, "Literal match is not allowed");
            }

            this.testAndConsumeTokenIf("+");
            const istr = this.consumeTokenAndGetValue();
            const [islit, ttype] = this.tryParseFollowConsType();

            return new ConstValueStructuredAssignment(islit ? new LiteralNaturalExpression(sinfo, istr) : new LiteralTypedNumericConstructorExpression(sinfo, istr, this.m_penv.SpecialNatSignature, ttype));
        }
        else if (this.testToken(TokenStrings.BigInt) || this.testFollows("+", TokenStrings.BigInt) || this.testFollows("-", TokenStrings.BigInt)) {
            if(!literalok) {
                this.raiseError(sinfo.line, "Literal match is not allowed");
            }

            const isneg = this.testToken("-");
            if(this.testToken("-") || this.testToken("+")) {
                this.consumeToken();
            }
            const istr = (isneg ? "-" : "") + this.consumeTokenAndGetValue();
            const [islit, ttype] = this.tryParseFollowConsType();

            return new ConstValueStructuredAssignment(islit ? new LiteralBigIntegerExpression(sinfo, istr) : new LiteralTypedNumericConstructorExpression(sinfo, istr, this.m_penv.SpecialBigIntSignature, ttype));
        }
        else if (this.testToken(TokenStrings.BigNat) || this.testFollows("+", TokenStrings.BigNat)) {
            if(!literalok) {
                this.raiseError(sinfo.line, "Literal match is not allowed");
            }

            this.testAndConsumeTokenIf("+");
            const istr = this.consumeTokenAndGetValue();
            const [islit, ttype] = this.tryParseFollowConsType();

            return new ConstValueStructuredAssignment(islit ? new LiteralBigNaturalExpression(sinfo, istr) : new LiteralTypedNumericConstructorExpression(sinfo, istr, this.m_penv.SpecialBigNatSignature, ttype));
        }
        else if (this.testToken(TokenStrings.Rational) || this.testFollows("+", TokenStrings.Rational) || this.testFollows("-", TokenStrings.Rational)) {
            if(!literalok) {
                this.raiseError(sinfo.line, "Literal match is not allowed");
            }

            const isneg = this.testToken("-");
            if(this.testToken("-") || this.testToken("+")) {
                this.consumeToken();
            }
            const istr = (isneg ? "-" : "") + this.consumeTokenAndGetValue();
            const [islit, ttype] = this.tryParseFollowConsType();

            return new ConstValueStructuredAssignment(islit ? new LiteralRationalExpression(sinfo, istr) : new LiteralTypedNumericConstructorExpression(sinfo, istr, this.m_penv.SpecialRationalSignature, ttype));
        }
        else if (this.testToken(TokenStrings.String)) {
            if(!literalok) {
                this.raiseError(sinfo.line, "Literal match is not allowed");
            }

            const sstr = this.consumeTokenAndGetValue(); //keep in escaped format
            return new ConstValueStructuredAssignment(new LiteralStringExpression(sinfo, sstr));
        }
        else if (this.testToken(TokenStrings.TypedString)) {
            if(!literalok) {
                this.raiseError(sinfo.line, "Literal match is not allowed");
            }

            const sstr = this.consumeTokenAndGetValue(); //keep in escaped format
            const ttype = this.parseFollowType();
                
            return new ConstValueStructuredAssignment(new LiteralTypedStringExpression(sinfo, sstr, ttype));
        }
        else if (this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Identifier)) {
            if(!literalok) {
                this.raiseError(sinfo.line, "Literal match is not allowed");
            }

            //it is a namespace access of some type
            const ns = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            if (this.testToken("<") || this.testToken("[") || this.testToken("(")) {
                this.raiseError(sinfo.line, "Expected a global constant expression");
            }
            
            //just a constant access
            return new ConstValueStructuredAssignment(new AccessNamespaceConstantExpression(sinfo, ns, name));
        }
        else if (this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Type ) || this.testToken(TokenStrings.Type)) {
            const ttype = this.parseTypeSignature(true);
            if (this.testFollows("::", TokenStrings.Identifier)) {
                if(!literalok) {
                    this.raiseError(sinfo.line, "Literal match is not allowed");
                }

                this.consumeToken();
                const name = this.consumeTokenAndGetValue();
                if (this.testToken("<") || this.testToken("[") || this.testToken("(")) {
                    this.raiseError(sinfo.line, "Expected a static field expression");
                }

                return new ConstValueStructuredAssignment(new AccessStaticFieldExpression(sinfo, ttype, name));
            }
            else if (this.testFollows("@", "{") || this.testFollows("#", "{")) {
                const isvalue = this.testToken("#");
                this.consumeToken();

                const assigns = this.parseListOf<[string, StructuredAssignment]>("{", "}", ",", () => {
                    this.ensureToken(TokenStrings.Identifier);
                    const name = this.consumeTokenAndGetValue();
    
                    this.ensureAndConsumeToken("=");
                    const subg = this.parseStructuredAssignment(this.getCurrentSrcInfo(), vars, trequired, literalok, decls);
    
                    return [name, subg];
                })[0];

                return new NominalStructuredAssignment(isvalue, ttype, assigns);
            }
            else if(ttype instanceof TemplateTypeSignature) {
                if(!literalok) {
                    this.raiseError(sinfo.line, "Literal match is not allowed");
                }

                return new ConstValueStructuredAssignment(new LiteralParamerterValueExpression(sinfo, ttype));
            }
            else {
                if(!literalok) {
                    this.raiseError(sinfo.line, "Literal match is not allowed");
                }

                this.raiseError(sinfo.line, "Unknown token sequence in parsing expression");
                return new ConstValueStructuredAssignment(new InvalidExpression(sinfo));
            }
        }
        else {
            if (this.testToken("let") || this.testToken("var")) {
                if (vars !== undefined) {
                    this.raiseError(sinfo.line, "Cannot mix var decl before and inside structured assign");
                }

                const isConst = this.testToken("let");
                this.consumeToken();

                this.ensureToken(TokenStrings.Identifier);
                const name = this.consumeTokenAndGetValue();

                if (decls.has(name)) {
                    this.raiseError(sinfo.line, "Variable is already defined in scope");
                }
                decls.add(name);

                const isopt = this.testAndConsumeTokenIf("?");
                let itype = this.m_penv.SpecialAutoSignature;
                if (trequired) {
                    this.ensureAndConsumeToken(":");
                    itype = this.parseTypeSignature(false);
                }
                else {
                    if (this.testAndConsumeTokenIf(":")) {
                        itype = this.parseTypeSignature(false);
                    }
                }

                return new VariableDeclarationStructuredAssignment(isopt, name, isConst, itype);
            }
            else {
                this.ensureToken(TokenStrings.Identifier);
                const name = this.consumeTokenAndGetValue();

                if (name === "_") {
                    const isopt = this.testAndConsumeTokenIf("?");

                    let itype = this.m_penv.SpecialAnySignature;
                    if (trequired) {
                        this.ensureAndConsumeToken(":");
                        itype = this.parseTypeSignature(false);
                    }
                    else {
                        if (this.testAndConsumeTokenIf(":")) {
                            itype = this.parseTypeSignature(false);
                        }
                    }

                    return new IgnoreTermStructuredAssignment(isopt, itype);
                }
                else {
                    const isopt = this.testAndConsumeTokenIf("?");

                    let itype = this.m_penv.SpecialAutoSignature;
                    if (trequired && vars !== undefined) {
                        this.ensureAndConsumeToken(":");
                        itype = this.parseTypeSignature(false);
                    }
                    else {
                        if (this.testAndConsumeTokenIf(":")) {
                            itype = this.parseTypeSignature(false);
                        }
                    }

                    if (vars !== undefined) {
                        if (decls.has(name)) {
                            this.raiseError(sinfo.line, "Variable is already defined in scope");
                        }
                        decls.add(name);

                        if (vars === "let") {
                            return new VariableDeclarationStructuredAssignment(isopt, name, true, itype);
                        }
                        else {
                            return new VariableDeclarationStructuredAssignment(isopt, name, false, itype);
                        }
                    }
                    else {
                        if (!this.m_penv.getCurrentFunctionScope().isVarNameDefined(name)) {
                            this.raiseError(sinfo.line, "Variable is not defined in scope");
                        }
                        
                        if(!(itype instanceof AutoTypeSignature)) {
                            this.raiseError(sinfo.line, "Cannot redeclare type of variable on assignment");
                        }

                        return new VariableAssignmentStructuredAssignment(isopt, name);
                    }
                }
            }
        }
    }

    private parseLineStatement(): Statement {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();

        const tk = this.peekToken();
        if (tk === ";") {
            this.consumeToken();
            return new EmptyStatement(sinfo);
        }
        else if (tk === "let" || tk === "var") {
            this.consumeToken();
            const isConst = tk === "let";

            if (this.testFollows("#", "[") || this.testFollows("#", "{") || this.testFollows("@", "[") || this.testFollows("@", "{")
                || this.testToken("(|")  || this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Type) || this.testToken(TokenStrings.Type)) {
                let decls = new Set<string>();
                const assign = this.parseStructuredAssignment(this.getCurrentSrcInfo(), isConst ? "let" : "var", false, false, decls);
                decls.forEach((dv) => {
                    if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(dv)) {
                        this.raiseError(line, "Variable name is already defined");
                    }
                    this.m_penv.getCurrentFunctionScope().defineLocalVar(dv);
                });

                this.ensureAndConsumeToken("=");
                const exp = this.parseExpression();
                this.ensureAndConsumeToken(";");

                return new StructuredVariableAssignmentStatement(sinfo, assign, exp);
            }
            else {
                let decls = new Set<string>();
                const assigns = this.parseEphemeralListOf(() => {
                    return this.parseStructuredAssignment(this.getCurrentSrcInfo(), isConst ? "let" : "var", false, false, decls);
                });

                if(assigns.length === 0 || (assigns.length === 1 && !(assigns[0] instanceof VariableDeclarationStructuredAssignment))) {
                    this.raiseError(sinfo.line, "Vacuous variable declaration");
                }
                
                let vars: {name: string, vtype: TypeSignature}[] = [];
                for(let i = 0; i < assigns.length; ++i) {
                    if (assigns[i] instanceof IgnoreTermStructuredAssignment) {
                        vars.push({name: "_", vtype: (assigns[i] as IgnoreTermStructuredAssignment).termType});
                    }
                    else if(assigns[i] instanceof VariableDeclarationStructuredAssignment) {
                        const dv = assigns[i] as VariableDeclarationStructuredAssignment;

                        if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(dv.vname)) {
                            this.raiseError(line, "Variable name is already defined");
                        }
                        this.m_penv.getCurrentFunctionScope().defineLocalVar(dv.vname);

                        vars.push({name: dv.vname, vtype: dv.vtype});
                    }
                    else {
                        this.raiseError(sinfo.line, "Cannot have structured multi-decls");
                    }
                }

                let exp: Expression[] | undefined = undefined;
                if(this.testAndConsumeTokenIf("=")) {
                    exp = this.parseEphemeralListOf(() => {
                        return this.parseExpression();
                    });
                }

                if ((exp === undefined && isConst)) {
                    this.raiseError(line, "Const variable declaration must include an assignment to the variable");
                }

                this.ensureAndConsumeToken(";");

                if(vars.length === 1) {
                    if (exp !== undefined && exp.length !== 1) {
                        this.raiseError(line, "Mismatch between variables declared and values provided");
                    }

                    const sexp = exp !== undefined ? exp[0] : undefined;
                    return new VariableDeclarationStatement(sinfo, vars[0].name, isConst, vars[0].vtype, sexp); 
                }
                else {
                    return new VariablePackDeclarationStatement(sinfo, isConst, vars, exp);
                }
            }
        }
        else if (this.testFollows("#", "[") || this.testFollows("#", "{") || this.testFollows("@", "[") || this.testFollows("@", "{")
                || this.testToken("(|")) {
            let decls = new Set<string>();
            const assign = this.parseStructuredAssignment(this.getCurrentSrcInfo(), undefined, false, false, decls);
            decls.forEach((dv) => {
                if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(dv)) {
                    this.raiseError(line, "Variable name is already defined");
                }
                this.m_penv.getCurrentFunctionScope().defineLocalVar(dv);
            });

            this.ensureAndConsumeToken("=");
            const exp = this.parseExpression();
            this.ensureAndConsumeToken(";");

            return new StructuredVariableAssignmentStatement(sinfo, assign, exp);
        }
        else if (tk === TokenStrings.Identifier) {
            let decls = new Set<string>();
            const assigns = this.parseEphemeralListOf(() => {
                return this.parseStructuredAssignment(this.getCurrentSrcInfo(), undefined, false, false, decls);
            });

            if(assigns.length === 0 || (assigns.length === 1 && !(assigns[0] instanceof VariableAssignmentStructuredAssignment))) {
                this.raiseError(sinfo.line, "Vacuous variable assignment");
            }
            
            let vars: string[] = [];
            for(let i = 0; i < assigns.length; ++i) {
                if (assigns[i] instanceof IgnoreTermStructuredAssignment) {
                    vars.push("_");
                }
                else if(assigns[i] instanceof VariableAssignmentStructuredAssignment) {
                    const av = assigns[i] as VariableAssignmentStructuredAssignment;

                    if (!this.m_penv.getCurrentFunctionScope().isVarNameDefined(av.vname)) {
                        this.raiseError(line, "Variable name is not defined");
                    }

                    vars.push(av.vname);
                }
                else {
                    this.raiseError(sinfo.line, "Cannot have structured multi-assigns");
                }
            }

            this.ensureAndConsumeToken("=");

            let exps: Expression[] = this.parseEphemeralListOf(() => {
                return this.parseExpression();
            });
            this.ensureAndConsumeToken(";");

            if(vars.length === 1) {
                if (exps.length !== 1) {
                    this.raiseError(line, "Mismatch between variables assigned and values provided");
                }

                return new VariableAssignmentStatement(sinfo, vars[0], exps[0]); 
            }
            else {
                return new VariablePackAssignmentStatement(sinfo, vars, exps);
            }
        }
        else if (tk === "return") {
            this.consumeToken();

            if(this.testAndConsumeTokenIf(";")) {
                return new ReturnStatement(sinfo, [new LiteralNoneExpression(sinfo)]);
            }
            else {
                const exps = this.parseEphemeralListOf(() => this.parseExpression());

                this.ensureAndConsumeToken(";");
                return new ReturnStatement(sinfo, exps);
            }
        }
        else if (tk === "yield") {
            this.consumeToken();

           const exps = this.parseEphemeralListOf(() => this.parseExpression());

            this.ensureAndConsumeToken(";");
            return new YieldStatement(sinfo, exps);
        }
        else if (tk === "abort") {
            this.consumeToken();

            this.ensureAndConsumeToken(";");
            return new AbortStatement(sinfo);
        }
        else if (tk === "assert") {
            this.consumeToken();
            let level = "debug" as BuildLevel;
            level = this.parseBuildInfo(level);

            const exp = this.parseExpression();

            this.ensureAndConsumeToken(";");
            return new AssertStatement(sinfo, exp, level);
        }
        else if (tk === "check") {
            this.consumeToken();

            const exp = this.parseExpression();

            this.ensureAndConsumeToken(";");
            return new CheckStatement(sinfo, exp);
        }
        else if (tk === "validate") {
            this.consumeToken();

            const exp = this.parseExpression();
            let err = new LiteralNoneExpression(sinfo);
            if (this.testAndConsumeTokenIf("or")) {
                this.ensureAndConsumeToken("return");
                err = this.parseExpression();
            }

            this.ensureAndConsumeToken(";");
            return new ValidateStatement(sinfo, exp, err);
        }
        else if (tk === "_debug") {
            this.consumeToken();

            let value = undefined;
            if (this.testToken("(")) {
                this.consumeToken();
                value = this.parseExpression();
                this.ensureAndConsumeToken(")");
            }

            this.ensureAndConsumeToken(";");
            return new DebugStatement(sinfo, value);
        }
        else if (this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Identifier)) {
            //it is a namespace function call
            const ns = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
            const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new PragmaArguments("no", []);
            const args = this.parseArguments("(", ")");

            return new NakedCallStatement(sinfo, new CallNamespaceFunctionOrOperatorExpression(sinfo, ns, name, targs, pragmas, args));
        }
        else if (this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Operator)) {
            //it is a namespace function call
            const ns = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new PragmaArguments("no", []);
            const args = this.parseArguments("(", ")");

            return new NakedCallStatement(sinfo, new CallNamespaceFunctionOrOperatorExpression(sinfo, ns, name, new TemplateArguments([]), pragmas, args));
        }
        else {
            //we should find a type (nominal here) and it is a static invoke or a structured assign
            const ttype = this.parseTypeSignature(false);

            if (this.testFollows("@", "{") || this.testFollows("#", "{")) {
                const isvalue = this.testToken("#");
                this.consumeToken();

                let decls = new Set<string>();
                const assigns = this.parseListOf<[string, StructuredAssignment]>("{", "}", ",", () => {
                    this.ensureToken(TokenStrings.Identifier);
                    const name = this.consumeTokenAndGetValue();
    
                    this.ensureAndConsumeToken("=");
                    const subg = this.parseStructuredAssignment(this.getCurrentSrcInfo(), undefined, false, false, decls);
    
                    return [name, subg];
                })[0];

                const assign = new NominalStructuredAssignment(isvalue, ttype, assigns);
                decls.forEach((dv) => {
                    if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(dv)) {
                        this.raiseError(line, "Variable name is already defined");
                    }
                    this.m_penv.getCurrentFunctionScope().defineLocalVar(dv);
                });

                this.ensureAndConsumeToken("=");
                const exp = this.parseExpression();
                this.ensureAndConsumeToken(";");

                return new StructuredVariableAssignmentStatement(sinfo, assign, exp);
            }
            else if(this.testFollows("::", TokenStrings.Identifier)) {
                this.consumeToken();
                const name = this.consumeTokenAndGetValue();
                const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
                const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new PragmaArguments("no", []);
                const args = this.parseArguments("(", ")");
                
                if (ttype instanceof MIRNominalType &&
                    ((ttype.trkey === "NSCore::Tuple" && name === "append") || (ttype.trkey === "NSCore::Record" && name === "join"))) {
                    this.raiseError(sinfo.line, "append/join do not have any effect as a standalone call");
                }

                return new NakedCallStatement(sinfo, new CallStaticFunctionOrOperatorExpression(sinfo, ttype, name, targs, pragmas, args));
            }
            else if(this.testFollows("::", TokenStrings.Operator)) {
                this.consumeToken();
                const name = this.consumeTokenAndGetValue();
                const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new PragmaArguments("no", []);
                const args = this.parseArguments("(", ")");

                return new NakedCallStatement(sinfo, new CallStaticFunctionOrOperatorExpression(sinfo, ttype, name, new TemplateArguments([]), pragmas, args));
            }
            else {
                this.raiseError(line, "Unknown statement structure");

                return new InvalidStatement(sinfo);
            }
        }
    }

    private parseBlockStatement(): BlockStatement {
        const sinfo = this.getCurrentSrcInfo();

        this.m_penv.getCurrentFunctionScope().pushLocalScope();
        let stmts: Statement[] = [];
        try {
            this.setRecover(this.scanMatchingParens("{", "}"));

            this.consumeToken();
            while (!this.testAndConsumeTokenIf("}")) {
                stmts.push(this.parseStatement());
            }

            this.m_penv.getCurrentFunctionScope().popLocalScope();

            if (stmts.length === 0) {
                this.raiseError(this.getCurrentLine(), "No empty blocks -- requires at least ';'");
            }

            this.clearRecover();
            return new BlockStatement(sinfo, stmts);
        }
        catch (ex) {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
            this.processRecover();
            return new BlockStatement(sinfo, [new InvalidStatement(sinfo)]);
        }
    }

    private parseIfElseStatement(): Statement {
        const sinfo = this.getCurrentSrcInfo();

        let conds: CondBranchEntry<BlockStatement>[] = [];

        this.ensureAndConsumeToken("if");
        this.ensureAndConsumeToken("(");
        const iftest = this.parseExpression();
        this.ensureAndConsumeToken(")");
        const ifbody = this.parseBlockStatement();

        conds.push(new CondBranchEntry<BlockStatement>(iftest, ifbody));

        while (this.testAndConsumeTokenIf("elif")) {
            this.ensureAndConsumeToken("(");
            const eliftest = this.parseExpression();
            this.ensureAndConsumeToken(")");
            const elifbody = this.parseBlockStatement();

            conds.push(new CondBranchEntry<BlockStatement>(eliftest, elifbody));
        }

        const elsebody = this.testAndConsumeTokenIf("else") ? this.parseBlockStatement() : undefined;

        return new IfElseStatement(sinfo, new IfElse<BlockStatement>(conds, elsebody));
    }

    private parseMatchGuard(sinfo: SourceInfo, matchtype: "type" | "case"): MatchGuard {
        if (this.testToken(TokenStrings.Identifier)) {
            const tv = this.consumeTokenAndGetValue();
            if (tv !== "_") {
                this.raiseError(sinfo.line, "Expected wildcard match");
            }

            return new WildcardMatchGuard();
        }

        let typecheck: TypeSignature | undefined = undefined;
        let layoutcheck: StructuredAssignment | undefined = undefined;
        let decls = new Set<string>();
        if (matchtype !== "case") {
            typecheck = this.parseTypeSignature(true);
        }
        else {
            let varinfo: "let" | "var" | undefined = undefined;
            if (this.testToken("var") || this.testToken("let")) {
                if (this.testToken("var")) {
                    varinfo = "var";
                }

                this.consumeToken();
            }

            layoutcheck = this.parseStructuredAssignment(sinfo, varinfo, true, true, decls);
        }

        let whencheck = undefined;
        if (this.testAndConsumeTokenIf("when")) {
            whencheck = this.parseSelectExpression(true);
        }

        if (matchtype === "type") {
            return new TypeMatchGuard(typecheck as TypeSignature, whencheck);
        }
        else {
            return new StructureMatchGuard(layoutcheck as StructuredAssignment, decls, whencheck);
        }
    }

    private parseMatchEntry<T>(sinfo: SourceInfo, matchtype: "type" | "case", actionp: () => T): MatchEntry<T> {
        if(!this.testToken(TokenStrings.Identifier)) {
            this.consumeToken();
        }

        const guard = this.parseMatchGuard(sinfo, matchtype);
        this.ensureAndConsumeToken("=>");
        const action = actionp();

        return new MatchEntry<T>(guard, action);
    }

    private parseMatchStatement(): Statement {
        const sinfo = this.getCurrentSrcInfo();

        this.ensureAndConsumeToken("switch");

        this.ensureAndConsumeToken("(");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(")");

        let entries: MatchEntry<BlockStatement>[] = [];
        this.ensureAndConsumeToken("{");
        while (this.testToken("type") || this.testToken("case") || (this.testToken(TokenStrings.Identifier) && this.peekTokenData() === "_")) {
            if (this.testToken("type")) {
                entries.push(this.parseMatchEntry<BlockStatement>(sinfo, "type", () => this.parseBlockStatement()));
            }
            else {
                entries.push(this.parseMatchEntry<BlockStatement>(sinfo, "case", () => this.parseBlockStatement()));
            }
        }
        this.ensureAndConsumeToken("}");

        return new MatchStatement(sinfo, mexp, entries);
    }

    private parseStatement(): Statement {
        if (this.testToken("if")) {
            return this.parseIfElseStatement();
        }
        else if (this.testToken("switch")) {
            return this.parseMatchStatement();
        }
        else {
            return this.parseLineStatement();
        }
    }

    private parseBody(bodyid: string, file: string): BodyImplementation {
        if (this.testToken("#")) {
            this.consumeToken();
            this.ensureToken(TokenStrings.Identifier);
            return new BodyImplementation(bodyid, file, this.consumeTokenAndGetValue());
        }
        else if (this.testToken("{")) {
            return new BodyImplementation(bodyid, file, this.parseBlockStatement());
        }
        else {
            return new BodyImplementation(bodyid, file, this.parseExpression());
        }
    }

    ////
    //Decl parsing

    private parseAttributes(): string[] {
        let attributes: string[] = [];
        while (Lexer.isAttributeKW(this.peekToken())) {
            attributes.push(this.consumeTokenAndGetValue());
        }
        return attributes;
    }

    private parseDeclPragmas(): [TypeSignature, string][] {
        let pragmas: [TypeSignature, string][] = [];
        while (this.testAndConsumeTokenIf("pragma")) {
            const ts = this.parseTypeSignature(false);
            const sl = this.testToken(TokenStrings.TypedString) ? this.consumeTokenAndGetValue() : "";

            pragmas.push([ts, sl]);
        }

        return pragmas;
    }

    private parseTemplateConstraint(hasconstraint: boolean): [TypeSignature, { ns: string, op: string, args: TypeSignature[] } | undefined] {
        if(!hasconstraint) {
            return [this.m_penv.SpecialAnySignature, undefined];
        }
        else {
            if(!this.testToken("operator")) {
                return [this.parseTypeSignature(false), undefined];
            }
            else {
                this.ensureAndConsumeToken("operator");

                const ns = this.testToken(TokenStrings.Namespace) ? this.consumeTokenAndGetValue() : this.m_penv.getCurrentNamespace();
                this.testAndConsumeTokenIf("::");

                const operator = this.consumeTokenAndGetValue();

                const args = this.parseListOf("(", ")", ",", () => {
                    return this.parseTypeSignature(false);
                });

                return [this.m_penv.SpecialAnySignature, { ns: ns, op: operator, args: args }];
            }
        }
    }

    private parseTermDeclarations(): TemplateTermDecl[] {
        let terms: TemplateTermDecl[] = [];
        if (this.testToken("<")) {
            terms = this.parseListOf<TemplateTermDecl>("<", ">", ",", () => {
                this.ensureToken(TokenStrings.Template);
                const templatename = this.consumeTokenAndGetValue();

                let isinfer = false;
                let defaulttype: TypeSignature | undefined = undefined;
                if (this.testAndConsumeTokenIf("=")) {
                    if (this.testAndConsumeTokenIf("?")) {
                        isinfer = true;
                    }
                    else {
                        defaulttype = this.parseTypeSignature(false);
                    }
                }

                const hasconstraint = this.testAndConsumeTokenIf("where");
                let specialConstraints = new Set<TemplateTermSpecialRestriction>();
                while (this.testToken("parsable") || this.testToken("validator") || this.testToken("struct") || this.testToken("entity")) {
                    if(this.testToken("parsable")) {
                        specialConstraints.add(TemplateTermSpecialRestriction.Parsable);
                    }
                    else if (this.testToken("validator")) {
                        specialConstraints.add(TemplateTermSpecialRestriction.Validator);
                    }
                    else if (this.testToken("struct")) {
                        specialConstraints.add(TemplateTermSpecialRestriction.Struct);
                    }
                    else {
                        if(!this.testToken("entity")) {
                            this.raiseError(this.getCurrentLine(), "Unknown template type constraint");
                        }

                        specialConstraints.add(TemplateTermSpecialRestriction.Entity);
                    } 
                }

                const [tconstraint, opconstraint] = this.parseTemplateConstraint(hasconstraint);
                return new TemplateTermDecl(templatename, specialConstraints, tconstraint, opconstraint, isinfer, defaulttype);
            })[0];
        }
        return terms;
    }

    private parseSingleTermRestriction(): TemplateTypeRestriction {
        this.ensureToken(TokenStrings.Template);
        const templatename = this.consumeTokenAndGetValue();
        const [tconstraint, opconstraint] = this.parseTemplateConstraint(true);

        return new TemplateTypeRestriction(new TemplateTypeSignature(templatename), tconstraint, opconstraint);
    }

    private parseTermRestrictionList(): TemplateTypeRestriction[] {
        const trl = this.parseSingleTermRestriction();
        if (this.testAndConsumeTokenIf("&&")) {
            const ands = this.parseTermRestrictionList();
            return [trl, ...ands];
        }
        else {
            return [trl];
        }
    }

    private parseTermRestriction(parencheck: boolean): TypeConditionRestriction | undefined {
        if(parencheck && !this.testToken("{")) {
            return undefined;
        }
        this.testAndConsumeTokenIf("{");

        if(parencheck) {
            this.testAndConsumeTokenIf("when");
        }
        
        const trl = this.parseTermRestrictionList();

        if(parencheck) {
            this.ensureAndConsumeToken("}");
        }

        return new TypeConditionRestriction(trl);
    }

    private parsePreAndPostConditions(sinfo: SourceInfo, argnames: Set<string>, rtype: TypeSignature): [PreConditionDecl[], PostConditionDecl[]] {
        let preconds: PreConditionDecl[] = [];
        try {
            this.m_penv.pushFunctionScope(new FunctionScope(new Set<string>(argnames), rtype, false));
            while (this.testToken("requires") || this.testToken("validate")) {
                const isvalidate = this.testToken("validate");
                this.consumeToken();
                
                let level: BuildLevel = isvalidate ? "release" : "debug";
                if (!isvalidate) {
                    level = this.parseBuildInfo(level);
                }

                const exp = this.parseSelectExpression(); //don't want to get the ExpOrExpression

                let err: Expression | undefined = undefined;
                if (isvalidate) {
                    err = new LiteralNoneExpression(sinfo);
                    if (this.testAndConsumeTokenIf("or")) {
                        this.ensureAndConsumeToken("return");
                        err = this.parseExpression();
                    }
                }

                preconds.push(new PreConditionDecl(sinfo, isvalidate, level, exp, err));

                this.ensureAndConsumeToken(";");
            }
        } finally {
            this.m_penv.popFunctionScope();
        }

        let postconds: PostConditionDecl[] = [];
        try {
            this.m_penv.pushFunctionScope(new FunctionScope(argnames, rtype, false));
            while (this.testToken("ensures")) {
                this.consumeToken();

                let level: BuildLevel = "debug";
                level = this.parseBuildInfo(level);

                const exp = this.parseExpression();
                postconds.push(new PostConditionDecl(sinfo, level, exp));

                this.ensureAndConsumeToken(";");
            }
        } finally {
            this.m_penv.popFunctionScope();
        }

        return [preconds, postconds];
    }

    private parseNamespaceUsing(currentDecl: NamespaceDeclaration) {
        //import NS {...} ;

        this.ensureAndConsumeToken("import");
        this.ensureToken(TokenStrings.Namespace);
        const fromns = this.consumeTokenAndGetValue();

        const names = this.parseListOf<string>("{", "}", ",", () => {
            return this.consumeTokenAndGetValue();
        })[0];

        this.ensureAndConsumeToken(";");

        if (currentDecl.checkUsingNameClash(names)) {
            this.raiseError(this.getCurrentLine(), "Collision between imported using names");
        }

        currentDecl.usings.push(new NamespaceUsing(fromns, names));
    }

    private parseNamespaceTypedef(currentDecl: NamespaceDeclaration) {
        //typedef NAME<T where C...> = TypeConstraint;

        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("typedef");
        this.ensureToken(TokenStrings.Type);
        const tyname = this.consumeTokenAndGetValue();

        if (currentDecl.checkDeclNameClash(currentDecl.ns, tyname)) {
            this.raiseError(this.getCurrentLine(), "Collision between typedef and other names");
        }

        const terms = this.parseTermDeclarations();

        this.ensureAndConsumeToken("=");
        const rpos = this.scanToken(";");
        if (rpos === this.m_epos) {
            this.raiseError(this.getCurrentLine(), "Missing ; on typedef");
        }

        if(this.testToken(TokenStrings.Regex)) {
            const vregex = this.consumeTokenAndGetValue();
            this.consumeToken();

            const re = BSQRegex.parse(vregex);
            if(typeof(re) === "string") {
                this.raiseError(this.getCurrentLine(), re);
            }

            const validator = new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), [], [], "vregex", new NominalTypeSignature("NSCore", ["Regex"]), new LiteralRegexExpression(sinfo, re as BSQRegex));
            const param = new FunctionParameter("arg", new NominalTypeSignature("NSCore", ["String"]), false, false, false, undefined);
            const acceptsbody = new BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "validator_accepts");
            const acceptsinvoke = new InvokeDecl(sinfo, this.m_penv.getCurrentFile(), [], "no", [], [], undefined, [param], undefined, undefined, new NominalTypeSignature("NSCore", ["Bool"]), [], [], false, new Set<string>(), acceptsbody);
            const accepts = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), [], "accepts", acceptsinvoke);
            const provides = [[new NominalTypeSignature("NSCore", ["Validator"]), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
            const validatortype = new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), [], [], [SpecialTypeCategory.ValidatorTypeDecl], currentDecl.ns, tyname, [], provides, [], new Map<string, StaticMemberDecl>().set("vregex", validator), new Map<string, StaticFunctionDecl>().set("accepts", accepts), new Map<string, StaticOperatorDecl[]>(), new Map<string, MemberFieldDecl>(), new Map<string, MemberMethodDecl>(), new Map<string, EntityTypeDecl>());

            currentDecl.objects.set(tyname, validatortype);
            this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + tyname, currentDecl.objects.get(tyname) as EntityTypeDecl);
            this.m_penv.assembly.addValidatorRegex(currentDecl.ns + "::" + tyname, re as BSQRegex);
        }
        else {
            const btype = this.parseTypeSignature(true);
            this.consumeToken();

            currentDecl.typeDefs.set(currentDecl.ns + "::" + tyname, new NamespaceTypedef(currentDecl.ns, tyname, terms, btype));
        }
    }

    private parseProvides(iscorens: boolean): [TypeSignature, TypeConditionRestriction | undefined][] {
        let provides: [TypeSignature, TypeConditionRestriction | undefined][] = [];
        if (this.testToken("provides")) {
            this.consumeToken();

            while (!this.testToken("{")) {
                this.consumeTokenIf(",");

                const pv = this.parseTypeSignature(false);
                let res: TypeConditionRestriction | undefined = undefined;
                if(this.testAndConsumeTokenIf("when")) {
                    res = this.parseTermRestriction(false);
                }
                provides.push([pv, res]);
            }
        }
        
        if (!iscorens) {
            provides.push([new NominalTypeSignature("NSCore", ["Object"]), undefined]);
        }

        return provides;
    }

    private parseConstMember(staticMembers: Map<string, StaticMemberDecl>, allMemberNames: Set<string>, attributes: string[], pragmas: [TypeSignature, string][]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] const NAME: T = exp;
        this.ensureAndConsumeToken("const");

        this.ensureToken(TokenStrings.Identifier);
        const sname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(":");
        const stype = this.parseTypeSignature(false);

        this.ensureAndConsumeToken("=");
        const value = this.parseExpression();

        this.ensureAndConsumeToken(";");

        if (allMemberNames.has(sname)) {
            this.raiseError(this.getCurrentLine(), "Collision between const and other names");
        }

        allMemberNames.add(sname);
        staticMembers.set(sname, new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, sname, stype, value));
    }

    private parseStaticFunction(staticFunctions: Map<string, StaticFunctionDecl>, allMemberNames: Set<string>, attributes: string[], pragmas: [TypeSignature, string][]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] function NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        this.ensureAndConsumeToken("function");
        const termRestrictions = this.parseTermRestriction(true);

        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        let recursive: "yes" | "no" | "cond" = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }
        const sig = this.parseInvokableCommon(InvokableKind.Basic, Parser.attributeSetContains("abstract", attributes), attributes, recursive, pragmas, terms, termRestrictions);

        if (allMemberNames.has(fname)) {
            this.raiseError(this.getCurrentLine(), "Collision between static and other names");
        }
        allMemberNames.add(fname);

        staticFunctions.set(fname, new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), attributes, fname, sig));
    }

    private parseStaticOperator(staticOperators: Map<string, StaticOperatorDecl[]>, allMemberNames: Set<string>, attributes: string[], pragmas: [TypeSignature, string][]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] operator NAME(params): type [requires...] [ensures...] { ... }
        this.ensureAndConsumeToken("operator");
        const termRestrictions = this.parseTermRestriction(true);

        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();
        let recursive: "yes" | "no" | "cond" = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }

        const ikind = attributes.includes("dynamic") ? InvokableKind.DynamicOperator : InvokableKind.StaticOperator;
        const sig = this.parseInvokableCommon(ikind, Parser.attributeSetContains("abstract", attributes), attributes, recursive, pragmas, [], termRestrictions);

        if (allMemberNames.has(fname)) {
            this.raiseError(this.getCurrentLine(), "Collision between static and other names");
        }
        allMemberNames.add(fname);

        if(!staticOperators.has(fname)) {
            staticOperators.set(fname, []);
        }
        (staticOperators.get(fname) as StaticOperatorDecl[]).push(new StaticOperatorDecl(sinfo, this.m_penv.getCurrentFile(), attributes, fname, sig));
    }

    private parseMemberField(memberFields: Map<string, MemberFieldDecl>, allMemberNames: Set<string>, attributes: string[], pragmas: [TypeSignature, string][]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] field NAME: T = exp;
        this.ensureAndConsumeToken("field");

        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(":");
        const stype = this.parseTypeSignature(false);
        let value: Expression | undefined = undefined;

        if (this.testAndConsumeTokenIf("=")) {
            value = this.parseExpression();
        }

        this.ensureAndConsumeToken(";");

        if (allMemberNames.has(fname)) {
            this.raiseError(this.getCurrentLine(), "Collision between const and other names");
        }

        memberFields.set(fname, new MemberFieldDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, fname, stype, value));
    }

    private parseMemberMethod(thisType: TypeSignature, memberMethods: Map<string, MemberMethodDecl>, allMemberNames: Set<string>, attributes: string[], pragmas: [TypeSignature, string][]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] [ref] method NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        const refrcvr = this.testAndConsumeTokenIf("ref");
        this.ensureAndConsumeToken("method");
        const termRestrictions = this.parseTermRestriction(true);

        this.ensureToken(TokenStrings.Identifier);
        const mname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        let recursive: "yes" | "no" | "cond" = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }
        const sig = this.parseInvokableCommon(InvokableKind.Member, Parser.attributeSetContains("abstract", attributes), attributes, recursive, pragmas, terms, termRestrictions, thisType);

        if (allMemberNames.has(mname)) {
            this.raiseError(this.getCurrentLine(), "Collision between static and other names");
        }
        allMemberNames.add(mname);

        memberMethods.set(mname, new MemberMethodDecl(sinfo, this.m_penv.getCurrentFile(), attributes, mname, refrcvr, sig));
    }

    private parseInvariantsInto(invs: InvariantDecl[]) {
        try {
            
            this.m_penv.pushFunctionScope(new FunctionScope(new Set<string>(), new NominalTypeSignature("NSCore", ["Bool"]), false));
            while (this.testToken("invariant")) {
                this.consumeToken();

                let level: BuildLevel = this.parseBuildInfo("debug");

                const sinfo = this.getCurrentSrcInfo();
                const exp = this.parseExpression();

                invs.push(new InvariantDecl(sinfo, level, exp));

                this.ensureAndConsumeToken(";");
            }
        } finally {
            this.m_penv.popFunctionScope();
        }
    }

    private parseOOPMembersCommon(thisType: TypeSignature, currentNamespace: NamespaceDeclaration, currentTypeNest: string[], currentTermNest: TemplateTermDecl[], 
        nestedEntities: Map<string, EntityTypeDecl>, invariants: InvariantDecl[], 
        staticMembers: Map<string, StaticMemberDecl>, staticFunctions: Map<string, StaticFunctionDecl>, staticOperators: Map<string, StaticOperatorDecl[]>, 
        memberFields: Map<string, MemberFieldDecl>, memberMethods: Map<string, MemberMethodDecl>) {
        let allMemberNames = new Set<string>();
        while (!this.testToken("}")) {
            const pragmas = this.parseDeclPragmas();
            const attributes = this.parseAttributes();

            if(this.testToken("entity")) {
                this.parseObject(currentNamespace, nestedEntities, currentTypeNest, currentTermNest);
            }
            else if (this.testToken("invariant")) {
                this.parseInvariantsInto(invariants);
            }
            else if (this.testToken("const")) {
                this.parseConstMember(staticMembers, allMemberNames, attributes, pragmas);
            }
            else if (this.testToken("function")) {
                this.parseStaticFunction(staticFunctions, allMemberNames, attributes, pragmas);
            }
            else if (this.testToken("operator")) {
                this.parseStaticOperator(staticOperators, allMemberNames, attributes, pragmas);
            }
            else if (this.testToken("field")) {
                this.parseMemberField(memberFields, allMemberNames, attributes, pragmas);
            }
            else {
                this.ensureToken("method");

                this.parseMemberMethod(thisType, memberMethods, allMemberNames, attributes, pragmas);
            }
        }
    }

    private parseConcept(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();

        //[attr] concept NAME[T where C...] provides {...}
        const pragmas = this.parseDeclPragmas();
        const attributes = this.parseAttributes();

        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("concept");
        this.ensureToken(TokenStrings.Type);

        const cname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        const provides = this.parseProvides(currentDecl.ns === "NSCore");

        try {
            this.setRecover(this.scanCodeParens());
            this.ensureAndConsumeToken("{");

            const thisType = new NominalTypeSignature(currentDecl.ns, [cname], terms.map((term) => new TemplateTypeSignature(term.name)));

            const invariants: InvariantDecl[] = [];
            const staticMembers = new Map<string, StaticMemberDecl>();
            const staticFunctions = new Map<string, StaticFunctionDecl>();
            const staticOperators = new Map<string, StaticOperatorDecl[]>();
            const memberFields = new Map<string, MemberFieldDecl>();
            const memberMethods = new Map<string, MemberMethodDecl>();
            const nestedEntities = new Map<string, EntityTypeDecl>();
            this.parseOOPMembersCommon(thisType, currentDecl, [cname], [...terms], nestedEntities, invariants, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods);

            this.ensureAndConsumeToken("}");

            if (currentDecl.checkDeclNameClash(currentDecl.ns, cname)) {
                this.raiseError(line, "Collision between concept and other names");
            }

            this.clearRecover();

            let tc: SpecialTypeCategory[] = [];
            if(OOPTypeDecl.attributeSetContains("parsable", attributes)) {
                tc.push(SpecialTypeCategory.ParsableTypeDecl);
            }

            if(currentDecl.ns === "NSCore") {
                if(cname === "Result") {
                    tc.push(SpecialTypeCategory.ResultDecl);
                }
            }


            const cdecl = new ConceptTypeDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, tc, currentDecl.ns, cname, terms, provides, invariants, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, nestedEntities);
            currentDecl.concepts.set(cname, cdecl);
            this.m_penv.assembly.addConceptDecl(currentDecl.ns + "::" + cname, cdecl);
        }
        catch (ex) {
            this.processRecover();
        }
    }

    private parseObject(currentDecl: NamespaceDeclaration, enclosingMap: Map<string, EntityTypeDecl> | undefined, currentTypeNest: string[], currentTermNest: TemplateTermDecl[]) {
        const line = this.getCurrentLine();

        //[attr] object NAME[T where C...] provides {...}
        const pragmas = this.parseDeclPragmas();
        const attributes = this.parseAttributes();

        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("entity");
        this.ensureToken(TokenStrings.Type);

        const ename = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        const provides = this.parseProvides(currentDecl.ns === "NSCore");

        try {
            this.setRecover(this.scanCodeParens());
            this.ensureAndConsumeToken("{");

            const thisType = new NominalTypeSignature(currentDecl.ns, [...currentTypeNest, ename], [...terms, ...currentTermNest].map((term) => new TemplateTypeSignature(term.name)));

            const invariants: InvariantDecl[] = [];
            const staticMembers = new Map<string, StaticMemberDecl>();
            const staticFunctions = new Map<string, StaticFunctionDecl>();
            const staticOperators = new Map<string, StaticOperatorDecl[]>();
            const memberFields = new Map<string, MemberFieldDecl>();
            const memberMethods = new Map<string, MemberMethodDecl>();
            const nestedEntities = new Map<string, EntityTypeDecl>();
            this.parseOOPMembersCommon(thisType, currentDecl, [...currentTypeNest, ename], [...currentTermNest, ...terms], nestedEntities, invariants, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods);

            this.ensureAndConsumeToken("}");

            if (currentDecl.checkDeclNameClash(currentDecl.ns, [...currentTypeNest, ename].join("::"))) {
                this.raiseError(line, "Collision between object and other names");
            }

            let specialinfo: SpecialTypeCategory[] = [];
            if(OOPTypeDecl.attributeSetContains("parsable", attributes)) {
                specialinfo.push(SpecialTypeCategory.ParsableTypeDecl);
            }

            if(currentDecl.ns === "NSCore") {
                if(ename === "StringOf") {
                    specialinfo.push(SpecialTypeCategory.StringOfDecl);
                }
                else if(ename === "DataString") {
                    specialinfo.push(SpecialTypeCategory.DataStringDecl);
                }
                else if(ename === "Buffer") {
                    specialinfo.push(SpecialTypeCategory.BufferDecl);
                }
                else if(ename === "DataBuffer") {
                    specialinfo.push(SpecialTypeCategory.DataBufferDecl);
                }
                else if(ename === "Ok") {
                    specialinfo.push(SpecialTypeCategory.ResultOkDecl);
                }
                else if(ename === "Err") {
                    specialinfo.push(SpecialTypeCategory.ResultErrDecl);
                }
                else if(ename === "Vector") {
                    specialinfo.push(SpecialTypeCategory.VectorTypeDecl);
                }
                else if(ename === "List") {
                    specialinfo.push(SpecialTypeCategory.ListTypeDecl);
                }
                else if(ename === "Stack") {
                    specialinfo.push(SpecialTypeCategory.StackTypeDecl);
                }
                else if(ename === "Queue") {
                    specialinfo.push(SpecialTypeCategory.QueueTypeDecl);
                }
                else if(ename === "Set") {
                    specialinfo.push(SpecialTypeCategory.SetTypeDecl);
                }
                else if(ename === "DynamicSet") {
                    specialinfo.push(SpecialTypeCategory.DynamicSetTypeDecl);
                }
                else if(ename === "Map") {
                    specialinfo.push(SpecialTypeCategory.MapTypeDecl);
                }
                else if(ename === "DynamicMap") {
                    specialinfo.push(SpecialTypeCategory.DynamicMapTypeDecl);
                }
                else {
                    //not special
                }
            }

            this.clearRecover();

            const fename = [...currentTypeNest, ename].join("::");
            const feterms = [...currentTermNest, ...terms];

            const edecl = new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, specialinfo, currentDecl.ns, fename, feterms, provides, invariants, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, nestedEntities);
            this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + fename, edecl);
            currentDecl.objects.set(ename, edecl);
            
            if(enclosingMap !== undefined) {
                enclosingMap.set(ename, edecl);
            }
        }
        catch (ex) {
            this.processRecover();
        }
    }

    private parseEnum(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();

        //[attr] enum NAME {...}
        const pragmas = this.parseDeclPragmas();
        const attributes = ["struct", ...this.parseAttributes()];

        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("enum");
        this.ensureToken(TokenStrings.Type);

        const ename = this.consumeTokenAndGetValue();
        const etype = new NominalTypeSignature(currentDecl.ns, [ename]);
        const simpleETypeResult = etype;
        const tryParseResult = new NominalTypeSignature("NSCore", ["Result"], [simpleETypeResult, new NominalTypeSignature("NSCore", ["String"])]);

        if (currentDecl.checkDeclNameClash(currentDecl.ns, ename)) {
            this.raiseError(line, "Collision between object and other names");
        }

        try {
            this.setRecover(this.scanCodeParens());

            const enums = this.parseListOf("{", "}", ",", () => {
                this.ensureToken(TokenStrings.Identifier);
                return this.consumeTokenAndGetValue();
            })[0];

            const cparam = new FunctionParameter("value", new NominalTypeSignature("NSCore", ["Int"]), false, false, false, undefined);
            const cbody = new BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "enum_create");
            const createdecl = new InvokeDecl(sinfo, this.m_penv.getCurrentFile(), [], "no", [], [], undefined, [cparam], undefined, undefined, simpleETypeResult, [], [], false, new Set<string>(), cbody);
            const create = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), ["private"], "create", createdecl);

            const tpparam = new FunctionParameter("str", new NominalTypeSignature("NSCore", ["String"]), false, false, false, undefined);
            const tpbody = new BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "enum_tryparse");
            const tryparsedecl = new InvokeDecl(sinfo, this.m_penv.getCurrentFile(), [], "no", [], [], undefined, [tpparam], undefined, undefined, tryParseResult, [], [], false, new Set<string>(), tpbody);
            const tryparse = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), ["private"], "tryParse", tryparsedecl);

            const provides = [[new NominalTypeSignature("NSCore", ["KeyType"]), undefined], [new NominalTypeSignature("NSCore", ["APIType"]), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
            const invariants: InvariantDecl[] = [];
            const staticMembers = new Map<string, StaticMemberDecl>();
            const staticFunctions = new Map<string, StaticFunctionDecl>().set("create", create).set("tryParse", tryparse);
            const staticOperators = new Map<string, StaticOperatorDecl[]>();
            const memberFields = new Map<string, MemberFieldDecl>();
            const memberMethods = new Map<string, MemberMethodDecl>();

            for(let i = 0; i < enums.length; ++i) {
                const enminit = new CallStaticFunctionOrOperatorExpression(sinfo, etype, "create", new TemplateArguments([]), new PragmaArguments("no", []), new Arguments([new PositionalArgument(false, false, new LiteralIntegerExpression(sinfo, (i + 1).toString()))]));
                const enm = new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), [], [], enums[i], etype, enminit);
                staticMembers.set(enums[i], enm);
            }

            if (currentDecl.checkDeclNameClash(currentDecl.ns, ename)) {
                this.raiseError(line, "Collision between object and other names");
            }

            this.clearRecover();
            currentDecl.objects.set(ename, new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, [SpecialTypeCategory.EnumTypeDecl], currentDecl.ns, ename, [], provides, invariants, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, new Map<string, EntityTypeDecl>()));
            this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + ename, currentDecl.objects.get(ename) as EntityTypeDecl);
        }
        catch (ex) {
            this.processRecover();
        }
    }

    private parseIdentifier(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();

        //[attr] identifier NAME = KeyType
        const pragmas = this.parseDeclPragmas();
        const attributes = this.parseAttributes();

        const sinfo = this.getCurrentSrcInfo();
       
        this.ensureAndConsumeToken("identifier");

        this.ensureToken(TokenStrings.Type);
        const iname = this.consumeTokenAndGetValue();
        if (currentDecl.checkDeclNameClash(currentDecl.ns, iname)) {
            this.raiseError(line, "Collision between object and other names");
        }

        const itype = new NominalTypeSignature(currentDecl.ns, [iname]);
        const simpleITypeResult = itype;

        this.ensureAndConsumeToken("=");
        const idval = this.parseTypeSignature(false);
        this.ensureAndConsumeToken(";");

        const param = new FunctionParameter("value", idval, false, false, false, undefined);
        const body = new BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "idkey_create");
        const createdecl = new InvokeDecl(sinfo, this.m_penv.getCurrentFile(), [], "no", [], [], undefined, [param], undefined, undefined, simpleITypeResult, [], [], false, new Set<string>(), body);
        const create = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), [], "create", createdecl);

        let provides = [[new NominalTypeSignature("NSCore", ["KeyType"]), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
        provides.push([new NominalTypeSignature("NSCore", ["APIType"]), new TypeConditionRestriction([new TemplateTypeRestriction(idval, new NominalTypeSignature("NSCore", ["APIType"]), undefined)])]);

        const invariants: InvariantDecl[] = [];
        const staticMembers = new Map<string, StaticMemberDecl>();
        const staticFunctions = new Map<string, StaticFunctionDecl>().set("create", create);
        const staticOperators = new Map<string, StaticOperatorDecl[]>();
        const memberFields = new Map<string, MemberFieldDecl>();
        const memberMethods = new Map<string, MemberMethodDecl>();

        currentDecl.objects.set(iname, new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, [SpecialTypeCategory.IdentifierTypeDecl], currentDecl.ns, iname, [], provides, invariants, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, new Map<string, EntityTypeDecl>()));
        this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + iname, currentDecl.objects.get(iname) as EntityTypeDecl);
    }

    private parseUnit(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();

        //[attr] unit NAME = Numeric
        const pragmas = this.parseDeclPragmas();
        const attributes = this.parseAttributes();

        const sinfo = this.getCurrentSrcInfo();
       
        this.ensureAndConsumeToken("unit");

        this.ensureToken(TokenStrings.Type);
        const iname = this.consumeTokenAndGetValue();
        if (currentDecl.checkDeclNameClash(currentDecl.ns, iname)) {
            this.raiseError(line, "Collision between object and other names");
        }

        const itype = new NominalTypeSignature(currentDecl.ns, [iname]);
        const simpleITypeResult = itype;

        this.ensureAndConsumeToken("=");
        const idval = this.parseTypeSignature(false);
        this.ensureAndConsumeToken(";");

        const cparam = new FunctionParameter("value", idval, false, false, false, undefined);
        const cbody = new BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "unit_create");
        const createdecl = new InvokeDecl(sinfo, this.m_penv.getCurrentFile(), [], "no", [], [], undefined, [cparam], undefined, undefined, simpleITypeResult, [], [], false, new Set<string>(), cbody);
        const create = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), [], "create", createdecl);

        const vparam = new FunctionParameter("x", itype, false, false, false, undefined);
        const vbody = new BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "unit_value");
        const valuedecl = new InvokeDecl(sinfo, this.m_penv.getCurrentFile(), [], "no", [], [], undefined, [vparam], undefined, undefined, idval, [], [], false, new Set<string>(), vbody);
        const value = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), [], "value", valuedecl);

        let provides = [[new NominalTypeSignature("NSCore", ["KeyType"]), new TypeConditionRestriction([new TemplateTypeRestriction(idval, new NominalTypeSignature("NSCore", ["KeyType"]), undefined)])]] as [TypeSignature, TypeConditionRestriction | undefined][];

        const invariants: InvariantDecl[] = [];
        const staticMembers = new Map<string, StaticMemberDecl>();
        const staticFunctions = new Map<string, StaticFunctionDecl>().set("create", create).set("value", value);
        const staticOperators = new Map<string, StaticOperatorDecl[]>();
        const memberFields = new Map<string, MemberFieldDecl>();
        const memberMethods = new Map<string, MemberMethodDecl>();

        //
        //TODO: maybe we want to auto generate operator definitions here
        //

        currentDecl.objects.set(iname, new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, [SpecialTypeCategory.UnitTypeDecl], currentDecl.ns, iname, [], provides, invariants, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, new Map<string, EntityTypeDecl>()));
        this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + iname, currentDecl.objects.get(iname) as EntityTypeDecl);
    }

    private parseNamespaceConst(currentDecl: NamespaceDeclaration) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] const NAME = exp;
        const pragmas = this.parseDeclPragmas();
        const attributes = this.parseAttributes();

        this.ensureAndConsumeToken("const");
        this.ensureToken(TokenStrings.Identifier);
        const gname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(":");
        const gtype = this.parseTypeSignature(false);

        this.ensureAndConsumeToken("=");
        const value = this.parseExpression();

        this.ensureAndConsumeToken(";");

        if (currentDecl.checkDeclNameClash(currentDecl.ns, gname)) {
            this.raiseError(this.getCurrentLine(), "Collision between global and other names");
        }

        currentDecl.consts.set(gname, new NamespaceConstDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, currentDecl.ns, gname, gtype, value));
    }

    private parseNamespaceFunction(currentDecl: NamespaceDeclaration) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] function NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        const pragmas = this.parseDeclPragmas();
        const attributes = this.parseAttributes();

        this.ensureAndConsumeToken("function");
        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();

        const terms = this.parseTermDeclarations();
        let recursive: "yes" | "no" | "cond" = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }
        const sig = this.parseInvokableCommon(InvokableKind.Basic, false, attributes, recursive, pragmas, terms, undefined);

        currentDecl.functions.set(fname, new NamespaceFunctionDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, fname, sig));
    }

    private parseNamespaceOperator(currentDecl: NamespaceDeclaration) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] operator [NS ::] NAME(params): type [requires...] [ensures...] { ... }
        const pragmas = this.parseDeclPragmas();
        const attributes = this.parseAttributes();

        this.ensureAndConsumeToken("operator");
        if (this.testToken("+") || this.testToken("-") || this.testToken("*") || this.testToken("/") ||
            this.testToken("==") || this.testToken("!=") || this.testToken("<") || this.testToken(">") || this.testToken("<=") || this.testToken(">=")) {
            const fname = this.consumeTokenAndGetValue();

            let recursive: "yes" | "no" | "cond" = "no";
            if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
                recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
            }

            const ns = this.m_penv.assembly.getNamespace("NSMain");
            const sig = this.parseInvokableCommon(InvokableKind.StaticOperator, false, attributes, recursive, pragmas, [], undefined);

            if (!currentDecl.operators.has(fname)) {
                currentDecl.operators.set(fname, []);
            }
            (ns.operators.get(fname) as NamespaceOperatorDecl[]).push(new NamespaceOperatorDecl(sinfo, this.m_penv.getCurrentFile(), attributes, "NSMain", fname, sig));
        }
        else {
            this.ensureToken(TokenStrings.Identifier);
            const fname = this.consumeTokenAndGetValue();

            let recursive: "yes" | "no" | "cond" = "no";
            if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
                recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
            }

            let ns = currentDecl;
            if(this.testToken(TokenStrings.Namespace)) {
                const nns = this.consumeTokenAndGetValue();
                this.ensureAndConsumeToken("::");

                ns = this.m_penv.assembly.getNamespace(nns);
            }

            const isabstract = OOPTypeDecl.attributeSetContains("abstract", attributes);
            const ikind = attributes.includes("dynamic") ? InvokableKind.DynamicOperator : InvokableKind.StaticOperator;
            const sig = this.parseInvokableCommon(ikind, isabstract, attributes, recursive, pragmas, [], undefined);

            let level = -1;
            if(isabstract) {
                level = Number.parseInt(this.consumeTokenAndGetValue());
                this.ensureAndConsumeToken(";");
            }

            if (!ns.operators.has(fname)) {
                ns.operators.set(fname, []);
            }
            (ns.operators.get(fname) as NamespaceOperatorDecl[]).push(new NamespaceOperatorDecl(sinfo, this.m_penv.getCurrentFile(), attributes, ns.ns, fname, sig, level));
        }
    }

    private parseEndOfStream() {
        this.ensureAndConsumeToken(TokenStrings.EndOfStream);
    }

    ////
    //Public methods

    parseCompilationUnitPass1(file: string, contents: string): boolean {
        this.setNamespaceAndFile("[No Namespace]", file);

        const lexer = new Lexer(contents);
        this.initialize(lexer.lex());

        //namespace NS; ...
        this.ensureAndConsumeToken("namespace");
        this.ensureToken(TokenStrings.Namespace);
        const ns = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(";");

        this.setNamespaceAndFile(ns, file);
        const nsdecl = this.m_penv.assembly.ensureNamespace(ns);

        let parseok = true;
        while (this.m_cpos < this.m_epos) {
            try {
                this.m_cpos = this.scanTokenOptions("function", "operator", "const", "typedef", "concept", "entity", "enum", "identifier", "unit");
                if (this.m_cpos === this.m_epos) {
                    const tokenIndexBeforeEOF = this.m_cpos - 2;
                    if (tokenIndexBeforeEOF >= 0 && tokenIndexBeforeEOF < this.m_tokens.length) {
                        const tokenBeforeEOF = this.m_tokens[tokenIndexBeforeEOF];
                        if (tokenBeforeEOF.kind === TokenStrings.Error) {
                            this.raiseError(tokenBeforeEOF.line, `Expected */ but found EOF`);
                        }
                    }
                    break;
                }

                if (this.testToken("function")  || this.testToken("const")) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.Identifier);
                    const fname = this.consumeTokenAndGetValue();
                    if (nsdecl.declaredNames.has(fname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }

                    nsdecl.declaredNames.add(ns + "::" + fname);
                }
                else if (this.testToken("operator")) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.Identifier);
                    const fname = this.consumeTokenAndGetValue();

                    if (!this.testToken("+") && !this.testToken("-") && !this.testToken("*") && !this.testToken("/") &&
                        !this.testToken("==") && !this.testToken("!=") && !this.testToken("<") && !this.testToken(">") && !this.testToken("<=") && !this.testToken(">=")) {
                        let nns = ns;
                        if (this.testToken(TokenStrings.Namespace)) {
                            nns = this.consumeTokenAndGetValue();
                        }

                        if (nns === ns) {
                            nsdecl.declaredNames.add(ns + "::" + fname);
                        }
                    }
                }
                else if (this.testToken("typedef") || this.testToken("enum") || this.testToken("identifier") || this.testToken("unit")) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.Type);
                    const tname = this.consumeTokenAndGetValue();
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }

                    nsdecl.declaredNames.add(ns + "::" + tname);
                }
                else if (this.testToken("concept") || this.testToken("entity")) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.Type);
                    const tname = this.consumeTokenAndGetValue();
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }

                    nsdecl.declaredNames.add(ns + "::" + tname);

                    this.parseTermDeclarations();
                    this.parseProvides(ns === "NSCore");
            
                    this.ensureToken("{"); //we should be at the opening left paren 
                    this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                }
                else {
                    this.raiseError(this.getCurrentLine(), "Failed to parse top-level namespace declaration");
                }
            }
            catch (ex) {
                this.m_cpos++;
                parseok = false;
            }
        }

        return parseok;
    }

    parseCompilationUnitPass2(file: string, contents: string): boolean {
        this.setNamespaceAndFile("[No Namespace]", file);
        const lexer = new Lexer(contents);
        this.initialize(lexer.lex());

        //namespace NS; ...
        this.ensureAndConsumeToken("namespace");
        this.ensureToken(TokenStrings.Namespace);
        const ns = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(";");

        this.setNamespaceAndFile(ns, file);
        const nsdecl = this.m_penv.assembly.ensureNamespace(ns);

        let importok = true;
        let parseok = true;
        while (this.m_cpos < this.m_epos) {
            const rpos = this.scanTokenOptions("function", "operator", "import", "typedef", "concept", "entity", "enum", "identifier", "unit", TokenStrings.EndOfStream);

            try {
                if (rpos === this.m_epos) {
                    break;
                }

                const tk = this.m_tokens[rpos].kind;
                importok = importok && tk === "import";
                if (tk === "import") {
                    if (!importok) {
                        this.raiseError(this.getCurrentLine(), "Using statements must come before other declarations");
                    }

                    this.parseNamespaceUsing(nsdecl);
                }
                else if (tk === "function") {
                    this.parseNamespaceFunction(nsdecl);
                }
                else if (tk === "operator") {
                    this.parseNamespaceOperator(nsdecl);
                }
                else if (tk === "global") {
                    this.parseNamespaceConst(nsdecl);
                }
                else if (tk === "typedef") {
                    this.parseNamespaceTypedef(nsdecl);
                }
                else if (tk === "concept") {
                    this.parseConcept(nsdecl);
                }
                else if (tk === "entity") {
                    this.parseObject(nsdecl, undefined, [], []);
                }
                else if (tk === "enum") {
                    this.parseEnum(nsdecl);
                }
                else if (tk === "identifier") {
                    this.parseIdentifier(nsdecl);
                }
                else if (tk === "unit") {
                    this.parseUnit(nsdecl);
                }
                else if (tk === TokenStrings.EndOfStream) {
                    this.parseEndOfStream();
                }
                else {
                    this.raiseError(this.getCurrentLine(), "Invalid top-level definiton");
                }
            }
            catch (ex) {
                this.m_cpos = rpos + 1;
                parseok = false;
            }
        }

        return parseok;
    }

    getParseErrors(): [string, number, string][] | undefined {
        return this.m_errors.length !== 0 ? this.m_errors : undefined;
    }
}

export { 
    SourceInfo, ParseError, Parser,
    unescapeLiteralString
};
