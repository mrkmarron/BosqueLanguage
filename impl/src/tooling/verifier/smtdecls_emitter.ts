//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { MIRAssembly, MIRConceptType, MIREntityType, MIREntityTypeDecl, MIRFieldDecl, MIRInvokeDecl, MIRRecordType, MIRSpecialTypeCategory, MIRTupleType, MIRType } from "../../compiler/mir_assembly";
import { constructCallGraphInfo, markSafeCalls } from "../../compiler/mir_callg";
import { MIRInvokeKey } from "../../compiler/mir_ops";
import { SMTBodyEmitter } from "./smtbody_emitter";
import { SMTTypeEmitter } from "./smttype_emitter";
import { SMTAssembly, SMTConstantDecl, SMTEphemeralListDecl, SMTFunction, SMTModelState, SMTRecordDecl, SMTTupleDecl } from "./smt_assembly";
import { SMTCallGeneral, SMTCallSimple, SMTConst, SMTExp, SMTLet, SMTVar, VerifierOptions } from "./smt_exp";

const BuiltinEntityDeclNames = [
    "None",
    "Bool",
    "Int",
    "Nat",
    "BigInt",
    "BigNat",
    "Rational",
    "Float",
    "Decimal",
    "String",
    "ISOTime", 
    "LogicalTime",
    "Regex"
];

class SMTEmitter {
    readonly temitter: SMTTypeEmitter;
    readonly bemitter: SMTBodyEmitter;
    readonly assembly: SMTAssembly;

    private lastVInvokeIdx = 0;
    private lastVOperatorIdx = 0;
    private lastVEntityUpdateIdx = 0;

    constructor(temitter: SMTTypeEmitter, bemitter: SMTBodyEmitter, assembly: SMTAssembly) {
        this.temitter = temitter;
        this.bemitter = bemitter;
        this.assembly = assembly;
    }

    private generateAPITypeConstructorFunction_Primitive(tt: MIRType, depthexp: SMTExp, widthexp: SMTExp): SMTExp {
        if (this.temitter.isType(tt, "NSCore::None")) {
            return new SMTConst("bsq_none@literal");
        }
        else if (this.temitter.isType(tt, "NSCore::Bool")) {
            return new SMTCallSimple("BBool@UFCons_API", [depthexp, widthexp]);
        }
        else if (this.temitter.isType(tt, "NSCore::Int")) {
            return new SMTCallSimple("BInt@UFCons_API", [depthexp, widthexp]);
        }
        else if (this.temitter.isType(tt, "NSCore::Nat")) {
            return new SMTCallSimple("BNat@UFCons_API", [depthexp, widthexp]);
        }
        else if (this.temitter.isType(tt, "NSCore::BigInt")) {
            return new SMTCallSimple("BBigInt@UFCons_API", [depthexp, widthexp]);
        }
        else if (this.temitter.isType(tt, "NSCore::BigNat")) {
            return new SMTCallSimple("BBigNat@UFCons_API", [depthexp, widthexp]);
        }
        else if (this.temitter.isType(tt, "NSCore::Float")) {
            return new SMTCallSimple("BFloat@UFCons_API", [depthexp, widthexp]);
        }
        else if (this.temitter.isType(tt, "NSCore::Decimal")) {
            return new SMTCallSimple("BDecimal@UFCons_API", [depthexp, widthexp]);
        }
        else if (this.temitter.isType(tt, "NSCore::Rational")) {
            return new SMTCallSimple("BRational@UFCons_API", [depthexp, widthexp]);
        }
        else {
            return new SMTCallSimple("BString@UFCons_API", [depthexp, widthexp]);
        }
    }

    private generateAPITypeConstructorFunction_TypedNumber(trgtType: MIRType, depthexp: SMTExp, widthexp: SMTExp): SMTExp {
        const tdecl = this.bemitter.assembly.entityDecls.get(trgtType.trkey) as MIREntityTypeDecl;
        
        const mf = this.bemitter.assembly.fieldDecls.get("value") as MIRFieldDecl;
        const cfun = tdecl.;
    }

    private generateAPITypeConstructorFunction_ValidatedString(trgtType: MIRType, depthexp: SMTExp, widthexp: SMTExp): SMTExp {
        
    }

    private generateAPITypeConstructorFunction_Tuple(trgtType: MIRType, depthexp: SMTExp, widthexp: SMTExp): SMTExp {
        
    }

    private generateAPITypeConstructorFunction_Record(trgtType: MIRType, depthexp: SMTExp, widthexp: SMTExp): SMTExp {
        
    }

    private generateAPITypeConstructorFunction_List(trgtType: MIRType, depthexp: SMTExp, widthexp: SMTExp): SMTExp {
        
    }

    private generateAPITypeConstructorFunction_Set(trgtType: MIRType, depthexp: SMTExp, widthexp: SMTExp): SMTExp {
        
    }

    private generateAPITypeConstructorFunction_Map(trgtType: MIRType, depthexp: SMTExp, widthexp: SMTExp): SMTExp {
        
    }

    private generateAPITypeConstructorFunction(trgtType: MIRType, depthexp: SMTExp, widthexp: SMTExp): SMTExp {
        xxxx;
    }

    private parseAPITypeConstructorFunction_Primitive(trgtType: MIRType, depthexp: SMTExp, widthexp: SMTExp): SMTExp {

    }

    private parseAPITypeConstructorFunction_TypedNumber(trgtType: MIRType, depthexp: SMTExp, widthexp: SMTExp): SMTExp {
        
    }

    private parseAPITypeConstructorFunction_ValidatedString(trgtType: MIRType, depthexp: SMTExp, widthexp: SMTExp): SMTExp {
        
    }

    private parseAPITypeConstructorFunction_Tuple(trgtType: MIRType, depthexp: SMTExp, widthexp: SMTExp): SMTExp {
        
    }

    private parseAPITypeConstructorFunction_Record(trgtType: MIRType, depthexp: SMTExp, widthexp: SMTExp): SMTExp {
        
    }

    private parseAPITypeConstructorFunction_List(trgtType: MIRType, depthexp: SMTExp, widthexp: SMTExp): SMTExp {
        
    }

    private parseAPITypeConstructorFunction_Set(trgtType: MIRType, depthexp: SMTExp, widthexp: SMTExp): SMTExp {
        
    }

    private parseAPITypeConstructorFunction_Map(trgtType: MIRType, depthexp: SMTExp, widthexp: SMTExp): SMTExp {
        
    }

    private parseAPIType(trgtType: MIRType, arg: string): SMTExp {
        xxxx;
    }

    private processISequenceTypeDecl(vdecl: MIREntityTypeDecl) {
        xxxx;
    }

    private processVectorTypeDecl(vdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
    
    private processListTypeDecl(vdecl: MIREntityTypeDecl) {
        xxxx;
    }
        
    private processStackTypeDecl(vdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
        
    private processQueueTypeDecl(vdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
       
    private processSetTypeDecl(vdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
        
    private processDynamicSetTypeDecl(vdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
        
    private processMapTypeDecl(vdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
    
    private processDynamicMapTypeDecl(vdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }

    private processEntityDecl(vdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }

    private processVirtualInvokes() {
        for(let i = this.lastVInvokeIdx; i < this.bemitter.requiredVirtualFunctionInvokes.length; ++i) {
            this.bemitter.generateVirtualFunctionInvoke(this.bemitter.requiredVirtualFunctionInvokes[i]);
        }
        this.lastVInvokeIdx = this.bemitter.requiredVirtualFunctionInvokes.length;

        for(let i = this.lastVOperatorIdx; i < this.bemitter.requiredVirtualOperatorInvokes.length; ++i) {
            this.bemitter.generateVirtualOperatorInvoke(this.bemitter.requiredVirtualOperatorInvokes[i]);
        }
        this.lastVOperatorIdx = this.bemitter.requiredVirtualOperatorInvokes.length;
    }

    private processVirtualEntityUpdates() {
        for(let i = this.lastVEntityUpdateIdx; i < this.bemitter.requiredUpdateVirtualEntity.length; ++i) {
            this.bemitter.generateUpdateEntityFieldVirtual(this.bemitter.requiredUpdateVirtualEntity[i]);
        }
        this.lastVInvokeIdx = this.bemitter.requiredUpdateVirtualEntity.length;
    }

    private initializeSMTAssembly(assembly: MIRAssembly, entrypoint: MIRInvokeKey, callsafety: Map<MIRInvokeKey, { safe: boolean, trgt: boolean }>, maxgas: number) {
        let doneset = new Set<MIRInvokeKey>();
        const cginfo = constructCallGraphInfo([entrypoint], assembly);
        const rcg = [...cginfo.topologicalOrder].reverse();

        for (let i = 0; i < rcg.length; ++i) {
            const cn = rcg[i];
            if(doneset.has(cn.invoke)) {
                continue;
            }

            const cscc = cginfo.recursive.find((scc) => scc.has(cn.invoke));
            const currentSCC = cscc || new Set<string>();
            let worklist = cscc !== undefined ? [...cscc].sort() : [cn.invoke];

            let gasmax: number | undefined = cscc !== undefined ? maxgas : 1;
            for (let gasctr = 1; gasctr <= gasmax; gasctr++) {
                for (let mi = 0; mi < worklist.length; ++mi) {
                    const ikey = worklist[mi];

                    let gas: number | undefined = undefined;
                    let gasdown: number | undefined = undefined;
                    if (gasctr !== gasmax) {
                        gas = gasctr;
                        gasdown = gasctr - 1;
                    }
                    else {
                        gasdown = gasmax - 1;
                    }

                    const idcl = (assembly.invokeDecls.get(ikey) || assembly.primitiveInvokeDecls.get(ikey)) as MIRInvokeDecl;
                    const finfo = this.bemitter.generateSMTInvoke(idcl, currentSCC, gas, gasdown);
                    this.processVirtualInvokes();
                    this.processVirtualEntityUpdates();

                    if (finfo !== undefined) {
                        if (finfo instanceof SMTFunction) {
                            this.assembly.functions.push(finfo);
                        }
                        else {
                            this.assembly.uninterpfunctions.push(finfo);
                        }
                    }

                    const rtype = this.temitter.getSMTTypeFor(this.temitter.getMIRType(idcl.resultType));
                    if(this.assembly.resultTypes.find((rtt) => rtt.ctype.name === rtype.name) === undefined) {
                        this.assembly.resultTypes.push(({hasFlag: false, rtname: idcl.resultType, ctype: rtype}));
                    }
                }

                if(cscc !== undefined) {
                    cscc.forEach((v) => doneset.add(v));
                }
            }
        }   

        this.bemitter.requiredLoadVirtualTupleIndex.forEach((rvlt) => this.assembly.functions.push(this.bemitter.generateLoadTupleIndexVirtual(rvlt)));
        this.bemitter.requiredLoadVirtualRecordProperty.forEach((rvlr) => this.assembly.functions.push(this.bemitter.generateLoadRecordPropertyVirtual(rvlr)));
        this.bemitter.requiredLoadVirtualEntityField.forEach((rvle) => this.assembly.functions.push(this.bemitter.generateLoadEntityFieldVirtual(rvle)));
        
        this.bemitter.requiredProjectVirtualTupleIndex.forEach((rvpt) => this.assembly.functions.push(this.bemitter.generateProjectTupleIndexVirtual(rvpt)));
        this.bemitter.requiredProjectVirtualRecordProperty.forEach((rvpr) => this.assembly.functions.push(this.bemitter.generateProjectRecordPropertyVirtual(rvpr)));
        this.bemitter.requiredProjectVirtualEntityField.forEach((rvpe) => this.assembly.functions.push(this.bemitter.generateProjectEntityFieldVirtual(rvpe)));
    
        this.bemitter.requiredUpdateVirtualTuple.forEach((rvut) => this.assembly.functions.push(this.bemitter.generateUpdateTupleIndexVirtual(rvut)));
        this.bemitter.requiredUpdateVirtualRecord.forEach((rvur) => this.assembly.functions.push(this.bemitter.generateUpdateRecordPropertyVirtual(rvur)));

        const mirep = assembly.invokeDecls.get(entrypoint) as MIRInvokeDecl;
        
        const iargs = mirep.params.map((param, i) => {
            const mirptype = this.temitter.getMIRType(param.type);

            const vname = this.temitter.mangle(param.name);
            const vtype = this.temitter.getSMTTypeFor(mirptype);
            const vexp = this.generateAPITypeConstructorFunction(mirptype, new SMTConst(`(_ bv${i} ${this.assembly.vopts.ISize})`), new SMTConst("BNat@zero"));

            return { vname: vname, vtype: vtype, vinit: vexp };
        });

        const restype = this.temitter.getMIRType(mirep.resultType);
        const rtype = this.temitter.getSMTTypeFor(restype);
        if (this.assembly.resultTypes.find((rtt) => rtt.ctype.name === rtype.name) === undefined) {
            this.assembly.resultTypes.push(({ hasFlag: false, rtname: mirep.resultType, ctype: rtype }));
        }

        assembly.entityDecls.forEach((edcl) => {
            const mirtype = this.temitter.getMIRType(edcl.tkey);
            const ttag = `TypeTag_${this.temitter.getSMTTypeFor(mirtype)}`;

            this.assembly.typeTags.push(ttag);
            if(assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::KeyType"))) {
                this.assembly.keytypeTags.push(ttag);
            }

            if(edcl.specialDecls.has(MIRSpecialTypeCategory.VectorTypeDecl)) {
                this.processVectorTypeDecl(edcl);
            }
            else if(edcl.specialDecls.has(MIRSpecialTypeCategory.ListTypeDecl)) {
                this.processListTypeDecl(edcl);
            }
            else if(edcl.specialDecls.has(MIRSpecialTypeCategory.StackTypeDecl)) {
                this.processStackTypeDecl(edcl);
            }
            else if(edcl.specialDecls.has(MIRSpecialTypeCategory.QueueTypeDecl)) {
                this.processQueueTypeDecl(edcl);
            }
            else if(edcl.specialDecls.has(MIRSpecialTypeCategory.SetTypeDecl)) {
                this.processSetTypeDecl(edcl);
            }
            else if(edcl.specialDecls.has(MIRSpecialTypeCategory.DynamicSetTypeDecl)) {
                this.processDynamicSetTypeDecl(edcl);
            }
            else if(edcl.specialDecls.has(MIRSpecialTypeCategory.MapTypeDecl)) {
                this.processMapTypeDecl(edcl);
            }
            else if(edcl.specialDecls.has(MIRSpecialTypeCategory.DynamicMapTypeDecl)) {
                this.processDynamicMapTypeDecl(edcl);
            }
            else {
                if(edcl.ns === "NSCore" && edcl.name === "ISequence") {
                    this.processISequenceTypeDecl(edcl);
                }
                else {
                    if(edcl.ns !== "NSCore" || BuiltinEntityDeclNames.find((be) => be[0] === edcl.name) === undefined) {
                        this.processEntityDecl(edcl);
                    }
                }
            }
        });

        this.bemitter.requiredSubtypeTagChecks.forEach((stc) => {
            const occ = stc.oftype.options[0] as MIRConceptType;
            for(let i = 0; i < occ.ckeys.length; ++i) {
                const atname = `AbstractTypeTag_${this.temitter.getSMTTypeFor(this.temitter.getMIRType(occ.ckeys[i]))}`;
                if(!this.assembly.abstractTypes.includes(atname)) {
                    this.assembly.abstractTypes.push(atname);
                }

                assembly.typeMap.forEach((mtype) => {
                    if(this.temitter.isUniqueType(mtype) && assembly.subtypeOf(mtype, stc.t)) {
                        const ttag = `TypeTag_${this.temitter.getSMTTypeFor(mtype)}`;

                        if(this.assembly.subtypeRelation.find((ee) => ee.ttype === ttag && ee.atype === atname) === undefined) {
                            const issub = assembly.subtypeOf(mtype, stc.oftype);
                            this.assembly.subtypeRelation.push({ttype: ttag, atype: atname, value: issub});
                        }
                    }
                });
            }
        });

        this.bemitter.requiredIndexTagChecks.forEach((itc) => {
            const itag = `TupleIndexTag_${itc.idx}`;
            if(!this.assembly.indexTags.includes(itag)) {
                this.assembly.indexTags.push(itag);
            }

            assembly.typeMap.forEach((mtype) => {
                if (this.temitter.isUniqueType(mtype) && assembly.subtypeOf(mtype, itc.oftype)) {
                    const ttype = mtype.options[0] as MIRTupleType;
                    const ttag = `TypeTag_${this.temitter.getSMTTypeFor(mtype)}`;

                    if (this.assembly.hasIndexRelation.find((ee) => ee.idxtag === itag && ee.atype === ttag) === undefined) {
                        const hasidx = itc.idx < ttype.entries.length;
                        this.assembly.hasIndexRelation.push({ idxtag: itag, atype: ttag, value: hasidx });
                    }
                }
            });
        });

        this.bemitter.requiredRecordTagChecks.forEach((rtc) => {
            const ptag = `RecordPropertyTag_${rtc.pname}`;
            if(!this.assembly.propertyTags.includes(ptag)) {
                this.assembly.propertyTags.push(ptag);
            }

            assembly.typeMap.forEach((mtype) => {
                if (this.temitter.isUniqueType(mtype) && assembly.subtypeOf(mtype, rtc.oftype)) {
                    const ttype = mtype.options[0] as MIRRecordType;
                    const ttag = `TypeTag_${this.temitter.getSMTTypeFor(mtype)}`;

                    if (this.assembly.hasPropertyRelation.find((ee) => ee.pnametag === ptag && ee.atype === ttag) === undefined) {
                        const haspname = ttype.entries.find((entry) => entry.name === rtc.pname) !== undefined;
                        this.assembly.hasPropertyRelation.push({ pnametag: ptag, atype: ttag, value: haspname });
                    }
                }
            });
        });

        assembly.tupleDecls.forEach((ttup) => {
            const mirtype = this.temitter.getMIRType(ttup.trkey);
            const ttag = `TypeTag_${this.temitter.getSMTTypeFor(mirtype)}`;
            const iskey = assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::KeyType"));
            const isapi = assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::APIType"));

            this.assembly.typeTags.push(ttag);
            if(iskey) {
                this.assembly.keytypeTags.push(ttag);
            }
            
            const smttype = this.temitter.getSMTTypeFor(mirtype);
            const ops = this.temitter.getSMTConstructorName(mirtype);
            const consargs = ttup.entries.map((entry, i) => {
                return { fname: this.temitter.generateTupleIndexGetFunction(ttup, i), ftype: this.temitter.getSMTTypeFor(entry.type) };
            });

            this.assembly.tupleDecls.push(new SMTTupleDecl(iskey, isapi, smttype.name, ttag, { cname: ops.cons, cargs: consargs }, ops.box, ops.bfield));
        });

        assembly.recordDecls.forEach((trec) => {
            const mirtype = this.temitter.getMIRType(trec.trkey);
            const ttag = `TypeTag_${this.temitter.getSMTTypeFor(mirtype)}`;
            const iskey = assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::KeyType"));
            const isapi = assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::APIType"));

            this.assembly.typeTags.push(ttag);
            if(iskey) {
                this.assembly.keytypeTags.push(ttag);
            }
            
            const smttype = this.temitter.getSMTTypeFor(mirtype);
            const ops = this.temitter.getSMTConstructorName(mirtype);
            const consargs = trec.entries.map((entry) => {
                return { fname: this.temitter.generateRecordPropertyGetFunction(trec, entry.name), ftype: this.temitter.getSMTTypeFor(entry.type) };
            });

            this.assembly.recordDecls.push(new SMTRecordDecl(iskey, isapi, smttype.name, ttag, { cname: ops.cons, cargs: consargs }, ops.box, ops.bfield));
        });

        assembly.ephemeralListDecls.forEach((ephl) => {
            const mirtype = this.temitter.getMIRType(ephl.trkey);
            
            const smttype = this.temitter.getSMTTypeFor(mirtype);
            const ops = this.temitter.getSMTConstructorName(mirtype);
            const consargs = ephl.entries.map((entry, i) => {
                return { fname: this.temitter.generateEphemeralListGetFunction(ephl, i), ftype: this.temitter.getSMTTypeFor(entry) };
            });

            this.assembly.ephemeralDecls.push(new SMTEphemeralListDecl(smttype.name, { cname: ops.cons, cargs: consargs }));
        });

        assembly.constantDecls.forEach((cdecl) => {
            const smtname = this.temitter.mangle(cdecl.gkey);
            const consf = this.temitter.mangle(cdecl.value);
            const ctype = this.temitter.getSMTTypeFor(this.temitter.getMIRType(cdecl.declaredType));
            this.assembly.constantDecls.push(new SMTConstantDecl(smtname, ctype, consf));
        });

        this.assembly.maskSizes = this.bemitter.maskSizes;

        const smtcall = this.temitter.mangle(mirep.key);
        const callargs = iargs.map((arg) => new SMTVar(arg.vname));
        const issafe = (callsafety.get(entrypoint) as {safe: boolean, trgt: boolean}).safe;

        let iexp: SMTExp | undefined = undefined;
        let argchk: SMTExp[] | undefined = undefined;
        if(issafe) {
            iexp = this.temitter.generateResultTypeConstructorSuccess(restype, new SMTCallSimple(smtcall, callargs));
        }
        else {
            iexp = new SMTCallGeneral(smtcall, callargs);
            if(mirep.preconditions !== undefined) {
                argchk = mirep.preconditions.map((pc) => {
                    const ispcsafe = (callsafety.get(pc) as {safe: boolean, trgt: boolean}).safe;
                    if(ispcsafe) {
                        return new SMTCallSimple(this.temitter.mangle(pc), callargs); 
                    }
                    else {
                        return new SMTLet(
                            "pcres",
                            new SMTCallGeneral(this.temitter.mangle(pc), callargs),
                            new SMTCallSimple("and", [
                                this.temitter.generateResultIsSuccessTest(this.temitter.getMIRType("NSCore::Bool"), new SMTVar("pcres")),
                                this.temitter.generateResultGetSuccess(this.temitter.getMIRType("NSCore::Bool"), new SMTVar("pcres"))
                            ])
                        )
                    }
                });
            }
        }
        
        this.assembly.model = new SMTModelState(iargs, argchk, this.temitter.generateResultType(restype), iexp);
    }

    static generateSMTAssemblyForValidate(assembly: MIRAssembly, vopts: VerifierOptions, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, maxgas: number): SMTAssembly {
        const callsafety = markSafeCalls([entrypoint], assembly, errorTrgtPos);

        const temitter = new SMTTypeEmitter(assembly, vopts);
        const bemitter = new SMTBodyEmitter(assembly, temitter, vopts, callsafety, errorTrgtPos);
        const smtassembly = new SMTAssembly(vopts);

        let smtemit = new SMTEmitter(temitter, bemitter, smtassembly);
        smtemit.initializeSMTAssembly(assembly, entrypoint, callsafety, maxgas);

        ////////////
        const mirep = assembly.invokeDecls.get(entrypoint) as MIRInvokeDecl;
        const restype = temitter.getMIRType(mirep.resultType);

        const eqerrexp = new SMTCallSimple("=", [new SMTVar("@smtres@"), smtemit.temitter.generateResultTypeConstructorError(restype, new SMTConst("ErrorID_Target"))]);
        smtemit.assembly.modes = {
            refute: new SMTCallSimple("not", [eqerrexp]),
            generate: eqerrexp,
            evaluate: ["[INVALID]", new SMTConst("bsq_none")]
        };

        return smtemit.assembly;
    }

    static generateSMTAssemblyEvaluate(assembly: MIRAssembly, vopts: VerifierOptions, entrypoint: MIRInvokeKey, args: string[], maxgas: number): SMTAssembly {
        const callsafety = markSafeCalls([entrypoint], assembly, { file: "[NO TARGET]", line: -1, pos: -1 });

        const temitter = new SMTTypeEmitter(assembly, vopts);
        const bemitter = new SMTBodyEmitter(assembly, temitter, vopts, callsafety, { file: "[NO TARGET]", line: -1, pos: -1 });
        const smtassembly = new SMTAssembly(vopts);

        let smtemit = new SMTEmitter(temitter, bemitter, smtassembly);
        smtemit.initializeSMTAssembly(assembly, entrypoint, callsafety, maxgas);

        ////////////
        
        const mirep = assembly.invokeDecls.get(entrypoint) as MIRInvokeDecl;

        smtemit.assembly.modes = {
            refute: new SMTConst("false"),
            generate: new SMTConst("false"),
            evaluate: [
                `${entrypoint}(${args.join(", ")})`,
                new SMTCallSimple(temitter.mangle(entrypoint), args.map((arg, i) => smtemit.parseAPIType(smtemit.temitter.getMIRType(mirep.params[i].type), arg)))
            ],
        };

        return smtemit.assembly;
    }
}

export {
    SMTEmitter
};
