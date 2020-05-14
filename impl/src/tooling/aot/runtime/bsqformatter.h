//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"
#include "bsqvalue.h"
#include "bsqkeyvalues.h"

#pragma once

/*
----
Bosque ByteBuffer/Buffer<T> Format:
**Metadata -- always in plain text bytes**
##bosque [enc] [compress]
[#Version# any string up to newline -- reccomended SemVer compat] 
[#Hash# SHA3-256 hash of content]
[#Layout# topo|flat]
[#Bytes# \d+]

**Content -- provided as noted in metadata**
[Types: 
{
    //define optional type aliases for use later
    Type -> Structure Mapping
}]
[Data: 
{
    //optional identifier based data to reference later for dedup representation
    !ID -> DATA 
}]
[Type: Type | Structure Mapping]
CONTENT_DATA

----
Bosque Typed Inline (String/ByteBuffer) Format:
CONTENT_DATA -- List<T>[] and Map<T>{} types are all inline

----
Bosque Relaxed Inline (String/ByteBuffer) Format -- parsing types cannot be ambigious (e.g. {f: Int, g: List<Int>} | {f: Int, g: List<Bool|Int>}) since now result is indeterminate (and potentially expensive to parse):
CONTENT_DATA -- List[] and Map{} types are all extracted as given by type OR as List<APIType>, Map<KeyType&APIType, APIType>
*/

#define PARSER_INTERNAL_CHECK(C, M) { if(!(C)) { printf("\"%s\" in %s on line %i\n", M, __FILE__, __LINE__); fflush(stdout); exit(1); } }
#define PARSER_PARSE_ERROR(M, L) throw BSQParseError(M, (L)->getLine(), (L)->computeContext())

#define LEX_CFLOW(OP) if (OP) { return; }

namespace BSQ
{
    
class BSQParseError
{
public:
const char* msg;
const size_t line;
const std::string context;

BSQParseError(const char* msg, size_t line, const std::string& context) : msg(msg), line(line), context(context) { ; }
};

enum APILexerToken
{
    Invalid,

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
    Enum,
    IDKey,
    Comma,
    Colon,
    Arrow,
    LBrack,
    RBrack,
    LBrace,
    RBrace,
    ListStart,
    ListEnd,
    MapStart,
    MapEnd,
    LParen,
    RParen,
    ResultOk,
    ResultErr,

    TYPE_TOKEN,
    NAME_TOKEN,

    EOF_TOKEN,
    ERROR
};

class LexerRegexs
{
public:
    static std::regex whitespaceRe; 
    static std::regex commentRe;
    static std::regex intRe;
    static std::regex bigintRe;
    static std::regex floatRe;
    static std::regex stringRe;
    static std::regex typedStringRe;
    static std::regex isotimeRe;
    static std::regex uuidRe;
    static std::regex logicaltimeRe;
    static std::regex hashRe;

    static std::regex nameRe;

    static std::regex newlineRe;
};

class APIType_TextLexer
{
private:
    const std::string* data;
    const char* pos;
    const char* max;

    APILexerToken ctoken;
    const char* end;

    size_t line;

    void updateFilePos(const std::cmatch& m)
    {
        this->line += std::count(this->pos, this->pos + m.length(), "\n");
    }

    void consumeWSAndComment() 
    {
        while(this->pos < this->max)
        {
            std::cmatch m;
            auto opos = this->pos;

            if (this->pos < this->max && std::regex_search(this->pos, this->max, m, LexerRegexs::whitespaceRe, std::regex_constants::match_continuous))
            {
                this->updateFilePos(m);
                this->pos += m.length();
            }

            if (this->pos < this->max && std::regex_search(this->pos, this->max, m, LexerRegexs::commentRe, std::regex_constants::match_continuous))
            {
                this->updateFilePos(m);
                this->pos += m.length();
            }

            if(this->pos == opos)
            {
                return;
            }
        }

        this->ctoken = APILexerToken::EOF_TOKEN;
    }

    bool checkMatch(const std::regex& re, APILexerToken token) 
    {
        std::cmatch m;
        bool mtch = std::regex_search(this->pos, this->max, m, LexerRegexs::whitespaceRe, std::regex_constants::match_continuous);
        if(mtch)
        {
            this->updateFilePos(m);

            this->ctoken = token;
            this->end = this->pos + m.length();
        }

        return mtch;
    }

    template <size_t n>
    bool checkLiteral(const char(&literal)[n], APILexerToken token) 
    {
        bool mtch = (std::distance(this->pos, this->max) >= n) && std::equal(&literal, &literal + n, this->pos);
        if(mtch)
        {
            this->ctoken = token;
            this->end = this->pos + n;
        }

        return mtch;
    }

    void advance()
    {
        this->ctoken = APILexerToken::Invalid;
        
        this->pos = this->end;
        this->end = nullptr;
    }

    void lexToken()
    {
        this->advance();
        this->consumeWSAndComment();

        LEX_CFLOW(this->checkLiteral("none", APILexerToken::None));
        LEX_CFLOW(this->checkLiteral("true", APILexerToken::True));
        LEX_CFLOW(this->checkLiteral("false", APILexerToken::False));

        LEX_CFLOW(this->checkMatch(LexerRegexs::intRe, APILexerToken::Int));
        LEX_CFLOW(this->checkMatch(LexerRegexs::bigintRe, APILexerToken::BigInt));
        LEX_CFLOW(this->checkMatch(LexerRegexs::floatRe, APILexerToken::Float64));
            LEX_CFLOW(this->checkMatch(LexerRegexs::stringRe, APILexerToken::String));
            LEX_CFLOW(this->checkMatch(LexerRegexs::typedStringRe, APILexerToken::SafeString));
            LEX_CFLOW(this->checkMatch(LexerRegexs::isotimeRe, APILexerToken::ISOTime));
            LEX_CFLOW(this->checkMatch(LexerRegexs::uuidRe, APILexerToken::UUID));
            LEX_CFLOW(this->checkMatch(LexerRegexs::logicaltimeRe, APILexerToken::LogicalTime));
            LEX_CFLOW(this->checkMatch(LexerRegexs::hashRe, APILexerToken::CryptoHash));

            LEX_CFLOW(this->checkLiteral(",", APILexerToken::Comma));
            LEX_CFLOW(this->checkLiteral(":", APILexerToken::Colon));
            LEX_CFLOW(this->checkLiteral("=>", APILexerToken::Arrow));

            LEX_CFLOW(this->checkLiteral("[", APILexerToken::LBrack));
            LEX_CFLOW(this->checkLiteral("]", APILexerToken::RBrack));
            LEX_CFLOW(this->checkLiteral("{", APILexerToken::LBrace));
            LEX_CFLOW(this->checkLiteral("}", APILexerToken::RBrace));

            LEX_CFLOW(this->checkLiteral("[|", APILexerToken::ListStart));
            LEX_CFLOW(this->checkLiteral("|]", APILexerToken::ListEnd));
            LEX_CFLOW(this->checkLiteral("{|", APILexerToken::MapStart));
            LEX_CFLOW(this->checkLiteral("|}", APILexerToken::MapEnd));
            LEX_CFLOW(this->checkLiteral("{|", APILexerToken::MapStart));
            LEX_CFLOW(this->checkLiteral("|}", APILexerToken::MapEnd));
            LEX_CFLOW(this->checkLiteral("(", APILexerToken::LParen));
            LEX_CFLOW(this->checkLiteral(")", APILexerToken::RParen));

            LEX_CFLOW(this->checkLiteral("ok(", APILexerToken::ResultOk));
            LEX_CFLOW(this->checkLiteral("err(", APILexerToken::ResultErr));

            LEX_CFLOW(this->checkMatch(LexerRegexs::nameRe, APILexerToken::NAME_TOKEN));

        this->ctoken = APILexerToken::ERROR;
    }

public:
    APIType_TextLexer(const std::string* data) 
        : data(data), pos(data->c_str()), max(data->c_str() + data->size()), ctoken(APILexerToken::Invalid), end(data->c_str()), line(1)
    { 
        this->lexToken();
    }

    size_t getLine() const
    {
        return this->line;
    }

    std::string computeContext() const
    { 
        return "[INVALID]"; 
    }

    APILexerToken peek() 
    {
        return this->ctoken;
    }

    void pop() 
    { 
        if(this->ctoken != APILexerToken::EOF_TOKEN)
        {
            this->lexToken();
        }
    }

    std::pair<const char*, const char*> read() 
    {
        PARSER_INTERNAL_CHECK(this->ctoken != APILexerToken::EOF_TOKEN && this->ctoken != APILexerToken::ERROR, "BAD TOKEN");

        std::make_pair(this->pos, this->end); 
    }
};

class BosqueAPIType_TextParser
{
private:
    APIType_TextLexer lexer;

public:
    BosqueAPIType_TextParser(const std::string* data) : lexer(data) { ; }

    Value parseNone();

    bool parseBool();
    int64_t parseInt();
    BSQBigInt* parseBigInt();
    double parseFloat64();
    
    BSQString* parseString();
    BSQSafeString* parseSafeString();

    BSQISOTime parseISOTime();
    BSQUUID parseUUID();
    BSQLogicalTime parseLogicalTime();
    BSQCryptoHash* parseCryptoHash();

    Enum,
    IDKey,
    Comma,
    Colon,
    Arrow,
    LBrack,
    RBrack,
    LBrace,
    RBrace,
    ListStart,
    ListEnd,
    MapStart,
    MapEnd,
    LParen,
    RParen,
    ResultOk,
    ResultErr,
};

} // namespace BSQ
