//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

type VerifierLevel = "Weak" | "Strong";

abstract class SMTTerm {
}

class SMTType extends SMTTerm {
    readonly name: string;
    
    constructor(name: string) {
        super();

        this.name = name;
    }
}

abstract class SMTExp extends SMTTerm {
    constructor() {
        super();
    }
}

class SMTVar extends SMTExp {
    readonly vname: string;

    constructor(vname: string) {
        super();

        this.vname = vname;
    }
}

class SMTConst extends SMTExp {
    readonly cname: string;

    constructor(cname: string) {
        super();

        this.cname = cname;
    }
}

class SMTCall extends SMTExp {
    readonly fname: string;
    readonly args: SMTExp[];

    constructor(fname: string, args: SMTExp[]) {
        super();

        this.fname = fname;
        this.args = args;
    }
}

class SMTLet extends SMTExp {
}

class SMTIf extends SMTExp {

}

class SMTCond extends SMTExp {

}

export {
    VerifierLevel,
    SMTType, SMTExp, SMTVar, SMTConst, SMTCall, SMTLet, SMTIf, SMTCond
};
