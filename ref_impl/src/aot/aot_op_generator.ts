//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { MIROp, MIROpTag, MIRLoadConst, MIRArgument, MIRRegisterArgument, MIRConstantNone, MIRConstantTrue, MIRConstantFalse, MIRConstantInt, MIRConstantArgument, MIRConstantString } from "../compiler/mir_ops";
import { MIRType } from "../compiler/mir_assembly";

class CodeGenerator {
    getArgType(arg: MIRArgument, vtypes: Map<string, MIRType>): MIRType {
        if (arg instanceof MIRRegisterArgument) {
            return vtypes.get(arg.nameID) as MIRType;
        }
        else {
            if (arg instanceof MIRConstantNone) {
                return this.typegen.noneType;
            }
            else if (arg instanceof MIRConstantTrue || arg instanceof MIRConstantFalse) {
                return this.typegen.boolType;
            }
            else if (arg instanceof MIRConstantInt) {
                return this.typegen.intType;
            }
            else {
                return this.typegen.stringType;
            }
        }
    }

    varToSMT2Name(varg: MIRRegisterArgument): string {
        return this.sanitizeName(varg.nameID);
    }

    generateConstantExp(cval: MIRConstantArgument): string {
        if (cval instanceof MIRConstantNone) {
            return "RuntimeValueEnvironment::none";
        }
        else if (cval instanceof MIRConstantTrue) {
            return "true";
        }
        else if (cval instanceof MIRConstantFalse) {
            return "false";
        }
        else if (cval instanceof MIRConstantInt) {
            return cval.value.slice(1, cval.value.length - 2);
        }
        else {
            assert(cval instanceof MIRConstantString);

            return (cval as MIRConstantString).value;
        }
    }

    generateStmt(op: MIROp, vtypes: Map<string, MIRType>, fromblck: string): string {
        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const lcv = (op as MIRLoadConst);
                vtypes.set(lcv.trgt.nameID, this.getArgType(lcv.src, vtypes));
                return `${this.varToSMT2Name(lcv.trgt)} = ${this.generateConstantExp(lcv.src)}`;
            }
            case MIROpTag.MIRLoadConstTypedString:  {
                return NOT_IMPLEMENTED<SMTExp>("MIRLoadConstTypedString");
            }
            case MIROpTag.MIRAccessConstantValue: {
                const acv = (op as MIRAccessConstantValue);
                vtypes.set(acv.trgt.nameID, this.assembly.typeMap.get((this.assembly.constantDecls.get(acv.ckey) as MIRConstantDecl).declaredType) as MIRType);
                return this.generateMIRAccessConstantValue(acv, vtypes);
            }
            case MIROpTag.MIRLoadFieldDefaultValue: {
                const ldv = (op as MIRLoadFieldDefaultValue);
                vtypes.set(ldv.trgt.nameID, this.assembly.typeMap.get((this.assembly.fieldDecls.get(ldv.fkey) as MIRFieldDecl).declaredType) as MIRType);
                return this.generateMIRLoadFieldDefaultValue(ldv, vtypes);
            }
            case MIROpTag.MIRAccessArgVariable: {
                const lav = (op as MIRAccessArgVariable);
                vtypes.set(lav.trgt.nameID, this.getArgType(lav.name, vtypes));
                return new SMTLet(this.varToSMT2Name(lav.trgt), this.argToSMT2Direct(lav.name), SMTFreeVar.generate());
            }
            case MIROpTag.MIRAccessLocalVariable: {
                const llv = (op as MIRAccessLocalVariable);
                vtypes.set(llv.trgt.nameID, this.getArgType(llv.name, vtypes));
                return new SMTLet(this.varToSMT2Name(llv.trgt), this.argToSMT2Direct(llv.name), SMTFreeVar.generate());
            }
            default: {
                return NOT_IMPLEMENTED
            }
        }
    }
}