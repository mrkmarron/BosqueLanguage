//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { Value, ValueOps, ListValue, FloatValue, RegexValue, CollectionValue, MapValue, TupleValue } from "./value";
import { raiseRuntimeErrorIf } from "./interpreter_environment";
import { MIRAssembly, MIRInvokePrimitiveDecl, MIREntityType, MIRTupleTypeEntry, MIRTupleType, MIRPCode, MIRType } from "../compiler/mir_assembly";
import { MIRInvokeKey, MIRResolvedTypeKey } from "../compiler/mir_ops";

function validateListStartEnd(lvals: Value[], start: Value, end: Value): [number, number] {
    raiseRuntimeErrorIf(start !== undefined && (start < 0 || start > lvals.length));
    raiseRuntimeErrorIf(end !== undefined && (end < 0 || end > lvals.length));

    const rstart = (start !== undefined ? start : 0) as number;
    const rend = (end !== undefined ? end : lvals.length) as number;
    raiseRuntimeErrorIf(rend < rstart);

    return [rstart, rend];
}

function createListOf(masm: MIRAssembly, oft: MIRType, values: Value[]): Value {
    return new ListValue(oft.options[0] as MIREntityType, values);
}

type InterpreterEntryPoint = (call: MIRInvokeKey, args: Value[]) => Value;
type BuiltinCallSig = (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>) => Value;

const BuiltinCalls = new Map<string, BuiltinCallSig>()
    .set("any_istype", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        throw new Error("This should always be converted to special op");
    })
    .set("any_as", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        throw new Error("This should always be converted to special op");
    })
    .set("any_tryas", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        throw new Error("This should always be converted to special op");
    })
    .set("any_defaultas", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        throw new Error("This should always be converted to special op");
    })
    .set("any_isnone", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        throw new Error("This should always be converted to special op");
    })
    .set("any_issome", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        throw new Error("This should always be converted to special op");
    })

    .set("bool_tryparse", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        if (args.get("str") === "true") {
            return true;
        }
        else if (args.get("str") === "false") {
            return false;
        }
        else {
            return undefined;
        }
    })

    .set("int_tryparse", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        return /^[-+]?(([0-9])|([1-9][0-9]+))$/.test(ValueOps.convertToBasicString(args.get("str"))) ? Number.parseInt(ValueOps.convertToBasicString(args.get("str"))) : undefined;
    })

    .set("string_tountyped", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        return ValueOps.convertToBasicString(args.get("this"));
    })
    .set("string_length", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        return ValueOps.convertToBasicString(args.get("this")).length;
    })
    .set("string_startsWith", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        return ValueOps.convertToBasicString(args.get("this")).startsWith(ValueOps.convertToBasicString(args.get("str")));
    })
    .set("string_endsWith", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        return ValueOps.convertToBasicString(args.get("this")).endsWith(ValueOps.convertToBasicString(args.get("str")));
    })
    .set("string_includes", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        return ValueOps.convertToBasicString(args.get("this")).includes(ValueOps.convertToBasicString(args.get("str")));
    })
    .set("string_replace", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        return ValueOps.convertToBasicString(args.get("this")).replace(new RegExp(ValueOps.convertToBasicString(args.get("str")), "g"), ValueOps.convertToBasicString(args.get("with")));
    })
    .set("string_trim", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        return ValueOps.convertToBasicString(args.get("this")).trim();
    })
    .set("string_split", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const splits = ValueOps.convertToBasicString(args.get("this")).split(ValueOps.convertToBasicString(args.get("with")));
        return createListOf(masm, masm.typeMap.get(inv.resultType) as MIRType, splits);
    })
    .set("string_reverse", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const val = ValueOps.convertToBasicString(args.get("this"));
        const chars: Array<string> = val.split("").reverse();
        return chars.join("");
    })
    .set("string_upperCase", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        return ValueOps.convertToBasicString(args.get("this")).toUpperCase();
    })
    .set("string_lowerCase", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        return ValueOps.convertToBasicString(args.get("this")).toLowerCase();
    })
    .set("string_concat", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        return (args.get("args") as ListValue).values.join("");
    })
    .set("float_tryparse", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        return /^[-+]?[0-9]*\.[0-9]+([eE][-+]?[0-9]+)?$/.test(ValueOps.convertToBasicString(args.get("str"))) ? new FloatValue(Number.parseFloat(ValueOps.convertToBasicString(args.get("str")))) : undefined;
    })
    .set("float_isnan", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        return Number.isNaN((args.get("this") as FloatValue).value);
    })
    .set("float_isinfinity", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        return !Number.isFinite((args.get("this") as FloatValue).value);
    })
    .set("float_negate", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const val = (args.get("this") as FloatValue).value;
        return new FloatValue(-val);
    })
    .set("float_square", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const val = (args.get("this") as FloatValue).value;
        return new FloatValue(val * val);
    })
    .set("float_sqrt", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const val = (args.get("this") as FloatValue).value;
        return new FloatValue(Math.sqrt(val));
    })
    .set("float_add", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const vals = (args.get("args") as ListValue).values.map((v) => (v as FloatValue).value);
        raiseRuntimeErrorIf(vals.length === 0);
        return new FloatValue(vals.reduce((acc, v) => acc + v));
    })
    .set("float_sub", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const v1 = args.get("v1") as FloatValue;
        const v2 = args.get("v2") as FloatValue;
        return new FloatValue(v1.value - v2.value);
    })
    .set("float_mult", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const vals = (args.get("args") as ListValue).values.map((v) => (v as FloatValue).value);
        raiseRuntimeErrorIf(vals.length === 0);
        return new FloatValue(vals.reduce((acc, v) => acc * v));
    })
    .set("float_div", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const v1 = args.get("v1") as FloatValue;
        const v2 = args.get("v2") as FloatValue;
        return new FloatValue(v1.value / v2.value);
    })
    .set("regex_tryparse", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        try {
            return new RegexValue(ValueOps.convertToBasicString(args.get("this")));
        }
        catch {
            return undefined;
        }
    })
    .set("regex_match", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const re = (args.get("this") as RegexValue).re;
        const str = ValueOps.convertToBasicString(args.get("str"));
        const start = args.get("start") as number | undefined || 0;
        const end = args.get("end") as number | undefined || str.length;

        re.lastIndex = 0;
        return re.test(str.substr(start, end));
    })

    .set("list_createofsize", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        let size = args.get("size") as number;
        let init = args.get("with") as Value;
        let vals: Value[] = [];
        for (let i = 0; i < size; ++i) {
            vals.push(init);
        }
        return createListOf(masm, masm.typeMap.get(inv.resultType) as MIRType, vals);
    })
    .set("list_empty", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        return (args.get("this") as ListValue).values.length === 0;
    })
    .set("list_size", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        return (args.get("this") as ListValue).values.length;
    })
    .set("list_count", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const pcode = (inv as MIRInvokePrimitiveDecl).pcodes.get("p") as MIRPCode;
        const cargs = pcode.cargs.map((carg) => args.get(carg) as Value);
        return (args.get("this") as ListValue).values.reduce((acc, v) => (acc as number) + (ValueOps.convertBoolOrNoneToBool(ep(pcode.code, [v, ...cargs])) ? 1 : 0), 0);
    })
    .set("list_has", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const argv = args.get("v");
        return (args.get("this") as ListValue).values.findIndex((v) => ValueOps.valueEqualTo(v, argv)) !== -1;
    })
    .set("list_any", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const pcode = (inv as MIRInvokePrimitiveDecl).pcodes.get("p") as MIRPCode;
        const cargs = pcode.cargs.map((carg) => args.get(carg) as Value);
        return (args.get("this") as ListValue).values.some((v) => ValueOps.convertBoolOrNoneToBool(ep(pcode.code, [v, ...cargs])));
    })
    .set("list_all", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const pcode = (inv as MIRInvokePrimitiveDecl).pcodes.get("p") as MIRPCode;
        const cargs = pcode.cargs.map((carg) => args.get(carg) as Value);
        return (args.get("this") as ListValue).values.every((v) => ValueOps.convertBoolOrNoneToBool(ep(pcode.code, [v, ...cargs])));
    })
    .set("list_find", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const pcode = (inv as MIRInvokePrimitiveDecl).pcodes.get("p") as MIRPCode;
        const cargs = pcode.cargs.map((carg) => args.get(carg) as Value);
        const idx = (args.get("this") as ListValue).values.findIndex((v) => ValueOps.convertBoolOrNoneToBool(ep(pcode.code, [v, ...cargs])));

        raiseRuntimeErrorIf(idx === -1);
        return (args.get("this") as ListValue).values[idx];
    })
    .set("list_findLast", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const pcode = (inv as MIRInvokePrimitiveDecl).pcodes.get("p") as MIRPCode;
        const cargs = pcode.cargs.map((carg) => args.get(carg) as Value);
        const idx = (args.get("this") as ListValue).values.reverse().findIndex((v) => ValueOps.convertBoolOrNoneToBool(ep(pcode.code, [v, ...cargs])));

        raiseRuntimeErrorIf(idx === -1);
        return (args.get("this") as ListValue).values[idx];
    })
    .set("list_tryFindLast", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const pcode = (inv as MIRInvokePrimitiveDecl).pcodes.get("p") as MIRPCode;
        const cargs = pcode.cargs.map((carg) => args.get(carg) as Value);
        const idx = (args.get("this") as ListValue).values.reverse().findIndex((v) => ValueOps.convertBoolOrNoneToBool(ep(pcode.code, [v, ...cargs])));

        return idx !== -1 ? (args.get("this") as ListValue).values[idx] : undefined;
    })
    .set("list_tryfind", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const pcode = (inv as MIRInvokePrimitiveDecl).pcodes.get("p") as MIRPCode;
        const cargs = pcode.cargs.map((carg) => args.get(carg) as Value);
        const idx = (args.get("this") as ListValue).values.findIndex((v) => ValueOps.convertBoolOrNoneToBool(ep(pcode.code, [v, ...cargs])));
        return idx !== -1 ? (args.get("this") as ListValue).values[idx] : undefined;
    })
    .set("list_defaultfind", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const pcode = (inv as MIRInvokePrimitiveDecl).pcodes.get("p") as MIRPCode;
        const cargs = pcode.cargs.map((carg) => args.get(carg) as Value);
        const idx = (args.get("this") as ListValue).values.findIndex((v) => ValueOps.convertBoolOrNoneToBool(ep(pcode.code, [v, ...cargs])));
        return idx !== -1 ? (args.get("this") as ListValue).values[idx] : args.get("default");
    })
    .set("list_filter", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const pcode = (inv as MIRInvokePrimitiveDecl).pcodes.get("p") as MIRPCode;
        const cargs = pcode.cargs.map((carg) => args.get(carg) as Value);
        const nvals = (args.get("this") as ListValue).values.filter((v) => ValueOps.convertBoolOrNoneToBool(ep(pcode.code, [v, ...cargs])));
        return createListOf(masm, masm.typeMap.get(inv.resultType) as MIRType, nvals);
    })
    .set("list_ofType", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const ttype = inv.binds.get("U") as MIRResolvedTypeKey;
        const nvals = (args.get("this") as ListValue).values.filter((v) => masm.subtypeOf(ValueOps.getValueType(v), masm.typeMap.get(ttype) as MIRType));
        return createListOf(masm, masm.typeMap.get(inv.resultType) as MIRType, nvals);
    })
    .set("list_map", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const pcode = (inv as MIRInvokePrimitiveDecl).pcodes.get("f") as MIRPCode;
        const cargs = pcode.cargs.map((carg) => args.get(carg) as Value);
        const nvals = (args.get("this") as ListValue).values.map((v) => ep(pcode.code, [v, ...cargs]));
        return createListOf(masm, masm.typeMap.get(inv.resultType) as MIRType, nvals);
    })
    .set("list_skipMap", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const pcode = (inv as MIRInvokePrimitiveDecl).pcodes.get("f") as MIRPCode;
        const cargs = pcode.cargs.map((carg) => args.get(carg) as Value);
        const nvals = (args.get("this") as ListValue).values.map((v) => ep(pcode.code, [v, ...cargs])).filter((v) => v !== undefined);
        return createListOf(masm, masm.typeMap.get(inv.resultType) as MIRType, nvals);
    })
    .set("list_flatMap", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const pcode = (inv as MIRInvokePrimitiveDecl).pcodes.get("f") as MIRPCode;
        const cargs = pcode.cargs.map((carg) => args.get(carg) as Value);
        const nvals = (args.get("this") as ListValue).values.map((v) => ValueOps.getContainerContentsEnumeration(ep(pcode.code, [v, ...cargs]) as CollectionValue));
        return createListOf(masm, masm.typeMap.get(inv.resultType) as MIRType, ([] as Value[]).concat(...nvals));
    })
    .set("list_transform", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const pcode = (inv as MIRInvokePrimitiveDecl).pcodes.get("f") as MIRPCode;
        const cargs = pcode.cargs.map((carg) => args.get(carg) as Value);
        const nvals = (args.get("this") as ListValue).values.map((v) => ep(pcode.code, [v, ...cargs]));
        return createListOf(masm, masm.typeMap.get(inv.resultType) as MIRType, nvals);
    })
    .set("list_project", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const map = args.get("map") as MapValue;
        const nvals = (args.get("this") as ListValue).values.map((v) => {
            const pv = map.lookup(ValueOps.getKeyForValue(v));
            raiseRuntimeErrorIf(pv === null);
            return pv as Value;
        });
        return createListOf(masm, masm.typeMap.get(inv.resultType) as MIRType, nvals);
    })
    .set("list_pairs", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const avals = (args.get("this") as ListValue).values;
        const skipIdentity = ValueOps.convertBoolOrNoneToBool(args.get("skipIdentity"));

        let res: Value[] = [];
        for (let i = 0; i < avals.length; ++i) {
            for (let j = i + (skipIdentity ? 1 : 0); j < avals.length; ++j) {
                const values = [avals[i], avals[j]];
                const types = values.map<MIRTupleTypeEntry>((v) => new MIRTupleTypeEntry(ValueOps.getValueType(v), false));

                res.push(new TupleValue(MIRTupleType.create(false, types), values));
            }
        }

        return createListOf(masm, masm.typeMap.get(inv.resultType) as MIRType, res);
    })
    .set("list_min", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const dmin = args.get("default");
        const avals = (args.get("this") as ListValue).values;
        raiseRuntimeErrorIf(dmin === undefined && avals.length === 0);

        return avals.reduce((acc, v) => Math.min(acc as number, v as number), (dmin !== undefined ? dmin : avals[0]) as number);
    })
    .set("list_max", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const dmax = args.get("default");
        const avals = (args.get("this") as ListValue).values;
        raiseRuntimeErrorIf(dmax === undefined && avals.length === 0);

        return avals.reduce((acc, v) => Math.max(acc as number, v as number), (dmax !== undefined ? dmax : avals[0]) as number);
    })
    .set("list_sum", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const dval = args.get("default");
        const avals = (args.get("this") as ListValue).values;
        raiseRuntimeErrorIf(dval === undefined && avals.length === 0);

        return avals.reduce((acc, v) => (acc as number) + (v as number), (dval !== undefined ? dval : avals[0]) as number);
    })
    .set("list_at", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const idx = args.get("idx") as number;
        const avals = (args.get("this") as ListValue).values;
        raiseRuntimeErrorIf(idx < 0 || avals.length <= idx);

        return avals[idx];
    })
    .set("list_tryat", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const idx = args.get("idx") as number;
        const avals = (args.get("this") as ListValue).values;

        return (0 <= idx || idx < avals.length) ? avals[idx] : undefined;
    })
    .set("list_defaultat", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const idx = args.get("idx") as number;
        const avals = (args.get("this") as ListValue).values;

        return (0 <= idx || idx < avals.length) ? avals[idx] : args.get("default");
    })
    .set("list_first", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const avals = (args.get("this") as ListValue).values;
        raiseRuntimeErrorIf(avals.length === 0);

        return avals[0];
    })
    .set("list_last", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const avals = (args.get("this") as ListValue).values;
        raiseRuntimeErrorIf(avals.length === 0);

        return avals[avals.length - 1];
    })
    .set("list_uniform", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const avals = (args.get("this") as ListValue).values;
        const rnd = args.get("rnd") as number;
        raiseRuntimeErrorIf(avals.length === 0);

        //TODO: this isn't really at uniform
        return avals[rnd % avals.length];
    })
    .set("list_indexof", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const argv = args.get("v");
        const avals = (args.get("this") as ListValue).values;
        const [start, end] = validateListStartEnd(avals, args.get("start"), args.get("end"));

        for (let i = start; i < end; ++i) {
            if (ValueOps.valueEqualTo(avals[i], argv)) {
                return i;
            }
        }
        return -1;
    })
    .set("list_indexoflast", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const argv = args.get("v");
        const avals = (args.get("this") as ListValue).values;
        const [start, end] = validateListStartEnd(avals, args.get("start"), args.get("end"));

        for (let i = end - 1; i >= start; --i) {
            if (ValueOps.valueEqualTo(avals[i], argv)) {
                return i;
            }
        }
        return -1;
    })
    .set("list_findindexof", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const pcode = (inv as MIRInvokePrimitiveDecl).pcodes.get("p") as MIRPCode;
        const cargs = pcode.cargs.map((carg) => args.get(carg) as Value);
        const avals = (args.get("this") as ListValue).values;
        const [start, end] = validateListStartEnd(avals, args.get("start"), args.get("end"));

        for (let i = start; i < end; ++i) {
            if (ValueOps.convertBoolOrNoneToBool(ep(pcode.code, [avals[i], ...cargs]))) {
                return i;
            }
        }
        return -1;
    })
    .set("list_findindexoflast", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const pcode = (inv as MIRInvokePrimitiveDecl).pcodes.get("p") as MIRPCode;
        const cargs = pcode.cargs.map((carg) => args.get(carg) as Value);
        const avals = (args.get("this") as ListValue).values;
        const [start, end] = validateListStartEnd(avals, args.get("start"), args.get("end"));

        for (let i = end - 1; i >= start; --i) {
            if (ValueOps.convertBoolOrNoneToBool(ep(pcode.code, [avals[i], ...cargs]))) {
                return i;
            }
        }
        return -1;
    })
    .set("list_sublist", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const avals = (args.get("this") as ListValue).values;
        const [start, end] = validateListStartEnd(avals, args.get("start"), args.get("end"));

        return createListOf(masm, masm.typeMap.get(inv.resultType) as MIRType, avals.slice(start, end));
    })
    .set("list_reverse", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const avals = [...(args.get("this") as ListValue).values].reverse();
        return createListOf(masm, masm.typeMap.get(inv.resultType) as MIRType, avals);
    })
    .set("list_zip", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const avals = (args.get("this") as ListValue).values;
        const maxidx = avals.map((v) => (v as ListValue).values.length).reduce((acc, v) => Math.min(acc, v), 0);

        const subltype = masm.typeMap.get(inv.binds.get("T") as string) as MIRType;

        if (maxidx === 0) {
            return createListOf(masm, masm.typeMap.get(inv.resultType) as MIRType, []);
        }
        else {
            let res: Value[] = [];
            for (let i = 0; i < maxidx; ++i) {
                const tres = avals.map((av) => (av as ListValue).values[i]);
                res.push(createListOf(masm, subltype, tres));
            }
            return createListOf(masm, masm.typeMap.get(inv.resultType) as MIRType, res);
        }
    })
    .set("list_zipwith", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const pcode = (inv as MIRInvokePrimitiveDecl).pcodes.get("f") as MIRPCode;
        const cargs = pcode.cargs.map((carg) => args.get(carg) as Value);
        const avals = (args.get("this") as ListValue).values;
        const maxidx = avals.map((v) => (v as ListValue).values.length).reduce((acc, v) => Math.min(acc, v), 0);

        if (maxidx === 0) {
            return createListOf(masm, masm.typeMap.get(inv.resultType) as MIRType, []);
        }
        else {
            let res: Value[] = [];
            for (let i = 0; i < maxidx; ++i) {
                const targs = avals.map((av) => (av as ListValue).values[i]);
                const tval = ep(pcode.code, [...targs, ...cargs]);
                res.push(tval);
            }
            return createListOf(masm, masm.typeMap.get(inv.resultType) as MIRType, res);
        }
    })
    .set("list_concat", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const avals = (args.get("this") as ListValue).values.map((v) => ValueOps.getContainerContentsEnumeration(v as CollectionValue));
        return createListOf(masm, masm.typeMap.get(inv.resultType) as MIRType, ([] as Value[]).concat(...avals));
    })
    .set("list_set", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const idx = args.get("idx") as number;
        const avals = (args.get("this") as ListValue).values;

        return createListOf(masm, masm.typeMap.get(inv.resultType) as MIRType, [...avals.slice(0, idx), args.get("v"), ...avals.slice(idx + 1)]);
    })
    .set("list_fill", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const avals = (args.get("this") as ListValue).values.map(() => args.get("v"));

        return createListOf(masm, masm.typeMap.get(inv.resultType) as MIRType, [...avals]);
    })
    .set("math_abs", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const n = args.get("n") as FloatValue;
        return new FloatValue(Math.abs(n.value));
    })
    .set("math_acos", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const x = args.get("x") as FloatValue;
        return new FloatValue(Math.acos(x.value));
    })
    .set("math_asin", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const x = args.get("x") as FloatValue;
        return new FloatValue(Math.asin(x.value));
    })
    .set("math_atan", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const x = args.get("x") as FloatValue;
        return new FloatValue(Math.atan(x.value));
    })
    .set("math_atan2", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const x = args.get("x") as FloatValue;
        const y = args.get("y") as FloatValue;
        return new FloatValue(Math.atan2(y.value, x.value));
    })
    .set("math_ceil", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const n = args.get("n") as FloatValue;
        return new FloatValue(Math.ceil(n.value));
    })
    .set("math_cos", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const x = args.get("x") as FloatValue;
        return new FloatValue(Math.cos(x.value));
    })
    .set("math_floor", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const n = args.get("n") as FloatValue;
        return new FloatValue(Math.floor(n.value));
    })
    .set("math_log", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const n = args.get("n") as FloatValue;
        return new FloatValue(Math.log(n.value));
    })
    .set("math_pow", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const b = args.get("b") as FloatValue;
        const e = args.get("e") as FloatValue;
        return new FloatValue(Math.pow(b.value, e.value));
    })
    .set("math_round", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const n = args.get("n") as FloatValue;
        return new FloatValue(Math.round(n.value));
    })
    .set("math_sin", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const x = args.get("x") as FloatValue;
        return new FloatValue(Math.sin(x.value));
    })
    .set("math_sqrt", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const x = args.get("x") as FloatValue;
        return new FloatValue(Math.sqrt(x.value));
    })
    .set("math_tan", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        const x = args.get("x") as FloatValue;
        return new FloatValue(Math.tan(x.value));
    })

    //////////////////
    //Some methods we want to make builtin but don't have a home for yet
    .set("misc_sigmasum", (ep: InterpreterEntryPoint, inv: MIRInvokePrimitiveDecl, masm: MIRAssembly, args: Map<string, Value>): Value => {
        let acc = 0.0;
        const vargs = (args.get("args") as ListValue).values;
        for (let i = 0; i < vargs.length; ++i) {
            acc += (vargs[i] as FloatValue).value;
        }
        return new FloatValue(acc);
    })
    ;

export { BuiltinCallSig, InterpreterEntryPoint, BuiltinCalls };
