//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"
#include "bsqvalue.h"
#include "bsqkeyvalues.h"

#include "bsqcustom/bsqlist_decl.h"
#include "bsqcustom/bsqlist_ops.h"
//TODO: Stack defs here
//TODO: Queue defs here
#include "bsqcustom/bsqset_decl.h"
#include "bsqcustom/bsqset_ops.h"
#include "bsqcustom/bsqmap_decl.h"
#include "bsqcustom/bsqmap_ops.h"

#pragma once

#define GET_RC_OPS(TAG) (bsq_ops[GET_MIR_TYPE_POSITION(TAG)])

#define PARSER_INTERNAL_CHECK(C, M) { if(C) { printf("\"%s\" in %s on line %i\n", M, __FILE__, __LINE__); fflush(stdout); exit(1); } }
#define PARSER_PARSE_ERROR(M, P) BSQParseError(M, P->line, P->column, P->computeContext())

#define PARSER_WHITESPACE_RE "^\\s+"
#define PARSER_COMMENT_RE ""
#define PARSER_INT_RE "^([+|-]?[0-9]+)"
#define PARSER_BIG_INT_RE "^([+|-]?[0-9]+)n"
#define PARSER_FLOAT_RE "^(([+|-]?([0-9]*\\.[0-9]+)|Infty)|NaN)"
#define PARSER_STRING_RE "^\"[^\"\\\\\\r\\n]*(?:\\\\(?:.|\\r?\\n)[^\"\\\\\\r\\n]*)*\""
#define TYPED_STRING_RE "^\'[^\"\\\\\\r\\n]*(?:\\\\(?:.|\\r?\\n)[^\"\\\\\\r\\n]*)*\'"
#define PARSER_NAME_RE "^[_a-zA-Z](_a-zA-Z0-9)*"

namespace BSQ
{
class Runtime
{
public:
//%%STATIC_STRING_DECLARE%%

//%%STATIC_INT_DECLARE%%

//%%EPHEMERAL_LIST_DECLARE
};

class BSQParseError
{
public:
const char* msg;
const size_t line;
const size_t column;
const std::string context;

BSQParseError(const char* msg, size_t line, size_t column, const std::string& context) : msg(msg), line(line), column(column), context(context) { ; }
};

enum APIFormatKind
{
    Invalid,

    Null,
    None,
    True,
    False,
    Int,
    BigInt,
    Float64,
    String,
    SafeString,
    ISOTime,
    UUID,
    LogicalTime,
    CryptoHash,
    MapEntry,
    Result,
    Comma,
    Colon,
    TupleStart,
    RecordStart,
    ListStart,
    MapStart,
    RBrackEnd,
    LBrackEnd,

    NAME_TOKEN,

    ERROR
};

template <BSQBufferEncoding enc, bool bmode>
class APITypeEncodingParser
{
public:
    APITypeEncodingParser(const std::string* data) { ; }

    std::string computeContext() { return "[INVALID]"; }

    APIFormatKind peekJSON() { return APIFormatKind::Invalid; }
    void pop() { ; }
    std::pair<char*, char*> read() { std::make_pair(nullptr, nullptr); }
};
/*
template <bool bmode>
class APITypeEncodingParser<BSQBufferEncoding::UTF8, bmode>
{
private:
    const std::string* data;
    std::string* pos;

    APIFormatKind ctoken;
    std::string* end;

    size_t line;
    size_t column;

    std::regex whitespaceRe; 
    std::regex commentRe;
    std::regex intRe;
    std::regex bigintRe;
    std::regex floatRe;
    std::regex stringRe;
    std::regex typedStringRe;
    std::regex nameRe;

    void lexToken()
    {
        if constexpr (bmode)
        {

        }
    }

public:
    APITypeEncodingParser(std::string* data) 
        : data(data), pos(data), ctoken(APIFormatKind::Invalid), end(data), line(1), column(1),
        whitespaceRe("^\\s+"), commentRe(""), intRe(""), bigintRe(""), floatRe("")
    { 
        ; 
    }

    std::string computeContext() 
    { 
        return "[INVALID]"; 
    }

    APIFormatKind peek() 
    {
        BSQ_ASSERT 
        return APIFormatKind::Invalid; 
    }
    void pop() { ; }
    std::pair<char*, char*> read() { std::make_pair(nullptr, nullptr); }
};
*/
} // namespace BSQ
