//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqformatter.h"

#include <charconv>

#ifdef _WIN32
#define timegm _mkgmtime
#endif

namespace BSQ
{
std::regex LexerRegexs::whitespaceRe("\\s+"); 
std::regex LexerRegexs::commentRe("/((\\/\\/.*)|(\\/\\*[\\s\\S]*?\\/\\*))/");
std::regex LexerRegexs::intRe("([+|-]?[0-9]+)");
std::regex LexerRegexs::bigintRe("([+|-]?[0-9]+)n");
std::regex LexerRegexs::floatRe("(([+|-]?([0-9]*\\.[0-9]+)|Infty)|NaN)");
std::regex LexerRegexs::stringRe("\"[^\"\\\\\\r\\n]*(?:\\\\(?:.|\\r?\\n)[^\"\\\\\\r\\n]*)*\"");
std::regex LexerRegexs::typedStringRe("\'[^\"\\\\\\r\\n]*(?:\\\\(?:.|\\r?\\n)[^\"\\\\\\r\\n]*)*\'");
std::regex LexerRegexs::isotimeRe("\\d{4}-\\d{2}-\\d{2}T\\d{2}:\\d{2}:\\d{2}.\\d{3}Z");
std::regex LexerRegexs::uuidRe("[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}");
std::regex LexerRegexs::logicaltimeRe("@[0-9]+");
std::regex LexerRegexs::hashRe("#[0-9a-fA-F]{64}");

std::regex LexerRegexs::nameRe("[_a-zA-Z](_a-zA-Z0-9)*");

std::regex LexerRegexs::newlineRe("\\n"); 


Value BosqueAPIType_TextParser::parseNone()
{
    this->lexer.pop();
    return nullptr;
}

bool BosqueAPIType_TextParser::parseBool()
{
    auto tok = this->lexer.peek();

    this->lexer.pop();
    return tok == APILexerToken::True ? true : false;
}

int64_t BosqueAPIType_TextParser::parseInt()
{
    int64_t res = INT64_MIN; //out of bounds so if parse fails this is unmodified and we still throw OOB
    auto rng = this->lexer.read();
    auto first = *rng.first == '+' ? (rng.first + 1) : rng.first;
    std::from_chars(first, rng.second, res);

    if(INT_OOF_BOUNDS(res))
    {
        PARSER_PARSE_ERROR("Int value is out-of-bounds", &this->lexer);
    }
    
    this->lexer.pop();
    return res;
}

BSQBigInt* BosqueAPIType_TextParser::parseBigInt()
{
    PARSER_PARSE_ERROR("BigInt is currently unsupported", &this->lexer);
}

double BosqueAPIType_TextParser::parseFloat64()
{
    double res = 0.0;
    auto rng = this->lexer.read();
    if(*(rng.second - 1) == 'N')
    {
        res = std::numeric_limits<double>::quiet_NaN();
    }
    else if(*(rng.second - 1) == 'y')
    {
        res = ((*rng.first == '-') ? -1 : 1) * std::numeric_limits<double>::infinity();
    }
    else
    {
        auto first = *rng.first == '+' ? (rng.first + 1) : rng.first;
        std::from_chars(first, rng.second, res);
    }

    this->lexer.pop();
    return res;
}

BSQString* BosqueAPIType_TextParser::parseString()
{
    auto rng = this->lexer.read();
    std::string str(rng.first + 1, rng.second - 1);

//
//TODO: unescape string contents
//

    this->lexer.pop();
    return BSQ_NEW_NO_RC(BSQString, move(str));
}

BSQSafeString* BosqueAPIType_TextParser::parseSafeString()
{

}

BSQISOTime BosqueAPIType_TextParser::parseISOTime()
{
    auto rng = this->lexer.read();

    std::tm time = { 0 };
    time.tm_year = std::stoi(rng.first) - 1900;
    time.tm_mon = std::stoi(rng.first + 5) - 1;
    time.tm_mday = std::stoi(rng.first + 8);
    time.tm_hour = std::stoi(rng.first + 11);
    time.tm_min = std::stoi(rng.first + 14);
    time.tm_sec = std::stoi(rng.first + 17);
    time.tm_isdst = 0;
    const int millis = std::stoi(rng.first + 20);
    uint64_t res = timegm(&time) * 1000 + millis;

    this->lexer.pop();
    return BSQISOTime(res);
}

BSQUUID BosqueAPIType_TextParser::parseUUID()
{
    xxxx;
}

BSQLogicalTime BosqueAPIType_TextParser::parseLogicalTime();

BSQCryptoHash* BosqueAPIType_TextParser::parseCryptoHash();
} // namespace BSQ
