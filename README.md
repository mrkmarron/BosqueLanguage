# Bosque Programming Language

[![Licensed under the MIT License](https://img.shields.io/badge/License-MIT-blue.svg)](https://github.com/Microsoft/BosqueLanguage/blob/master/LICENSE.txt)
[![PR's Welcome](https://img.shields.io/badge/PRs%20-welcome-brightgreen.svg)](#contribute)
[![Build Status](https://dev.azure.com/bosquepl/BosqueDevOps/_apis/build/status/Microsoft.BosqueLanguage?branchName=master)](https://dev.azure.com/bosquepl/BosqueDevOps/_build/latest?definitionId=1&branchName=master)

The Bosque programming language is a breakthrough research project from [_Microsoft Research_](https://www.microsoft.com/en-us/research/project/bosque-programming-language/). Bosque simultaneously supports a high productivity development experience expected by modern cloud developers, coming from say a TypeScript/Node stack, while also providing a resource efficient and predictable runtime with a performance profile similar to a native C++ application. Beyond supporting these, previously conflicting objectives in one language, Bosque also brings an unprecedented tooling ecosystem including zero-effort verification, symbolic testing, dependency management validation, time-travel debugging, and more. 

Small samples of code and unique Bosque tooling are below in the [Code Snippets](#Code-Snippets) and [Tooling](#Tooling) sections. A rundown of notable and/or unique features in the Bosque language is provided in the [language overview section 0](docs/language/overview.md#0-Highlight-Features).
For a look at how the language works and flows _in the large_ please see the code for a [simple tic-tac-toe](ref_impl/src/test/apps/tictactoe/main.bsq) program.

**Note:** This repository and code represent an alpha state. This means that the language is subject to revision, there are bugs and missing functionality, and the performance is limited. Thus, we **do not** recommend the use of the Bosque language for _any_ production work and instead encourage experimentation only with small/experimental side projects at this point in time.

## Documentation

* [Language Docs](docs/language/overview.md)
* [Library Docs](docs/libraries/overview.md)
* Tutorials - _Coming Soon!_
* [Technical Papers](docs/papers/publist.md)
* [Contribution guidelines](CONTRIBUTING.md)

## Code Snippets

**Add 2 numbers:**

```none
function add2(x: Int, y: Int): Int {
    return x + y;
}

add2(2, 3)     //5
add2(x=2, y=3) //5
add2(y=2, 5)   //7
```

**All odd check using rest parameters and lambda:**

```none
function allOdd(...args: List<Int>): Bool {
    return args->all(fn(x) => Math::mod(x, 2) == 1);
}

allOdd(1, 3, 4) //false
```

**Sign (with optional argument):**

```none
function sign(x?: Int): Int {
    var! y: Int;

    if(x == none || x == 0) {
        y = 0;
    }
    else {
        y = (x > 0) ? 1 : -1;
    }

    return y;
}

sign(5)    //1
sign(-5)   //-1
sign()     //0
```

**Nominal Types Data Invariants:**
[TESTS NEEDED]
```
concept WithName {
    invariant $name != "";

    field name: String;
}

concept Greeting {
    abstract method sayHello(): String;

    virtual method sayGoodbye(): String {
        return "goodbye";
    }
}

entity genericGreeting provides Hello {
    const instance: genericGreeting = genericGreeting@{};

    override method sayHello: String {
        return "hello world";
    }
}

entity namedGreeting provides WithName, Hello {
    override method sayHello: String {
        return String::concat("hello", " ", this.name);
    }
}

genericGreeting@{}->sayHello()        //"hello world"
genericGreeting::instance->sayHello() //"hello world"

namedGreeting@{}->sayHello()           //type error no value provided for "name" field
namedGreeting@{name=""}->sayHello()    //invariant error
namedGreeting@{name="bob"}->sayHello() //"hello bob"
```

**Validated and Typed Strings:**
[TESTS NEEDED]
```
typedef Letters4 = /\w\w\w\w/;
typedef Digits4 = /\d\d\d\d/;

function fss(s1: SafeString<Digits4>): Bool {
    return s1->rawString() == "1234";
}

Digits4::accepts("abcd") //false
Digits4::accepts("1234") //true

fss("1234")                           //type error String is not a SafeString
fss(SafeString<Letters4>::as("abcd")) //type error incompatible SafeString types
fss(Digits4'abcd')                    //type error 'abcd' is incompatible with Digits4 
fss(SafeString<Digits4>::as("abcd"))  //runtime error 'abcd' is incompatible with Digits4

fss(SafeString<Digits4>::as("1234"))  //true
```

```
entity ErrorCode provides Parsable {
    field code: Int;
    field name: String;

    override static tryParse(err: String): Result<Any, String> {
        return switch(err) {
            case "IO"     => Result<Any, String>::ok(ErrorCode@{code=1, name=err})
            case "Assert" => Result<Any, String>::ok(ErrorCode@{code=2, name=err})
            case _        => Result<Any, String>::err("Unknown error")
        }
    }
}

function isIOErr(s: StringOf<ErrorCode>): ErrorCode {
    return s == ErrorCode'IO';
}

isIOErr("IO")                             //type error not a StringOf<ErrorCode>
isIOErr(ErrorCode'Input')                 //type error not a valid ErrorCode string
isIOErr(StringOf<ErrorCode>::as('Input')) //runtime error not a valid ErrorCode string

isIOErr(ErrorCode'Assert')             //false
isIOErr(StringOf<ErrorCode>::as('IO')) //true

var ec: ErrorCode = StringOf<ErrorCode>@'IO';
assert(ec.code == 1); //true
```

**Structural, Nominal, and Union Types**
[TESTS NEEDED]
```
entity Person {
    field name: String; 
}

function foo(arg?: {f: Int, n?: String} | String | Person): String {
    if(arg->is<Tuple>()) {
        return arg.n ?| "Blank";
    }
    else {
        return switch(arg) {
            type None => "N/A"
            type String => arg
            type Person => arg.name
        }
    }
}

foo()                    //"N/A"
foo("Bob")               //Bob
foo(Person@{name="Bob"}) //Bob
foo({f=5})               //"Blank"
foo({f=1, n="Bob"})      //"Bob"

Foo({g=1, n="Bob"}) //Missing f property
foo(none) //Error
```

**Pre/Post Conditions**
```
entity Animal {
    invariant $says != "";

    field says: String;
}

function createAnimal(catchPhrase: String): Animal
{
    return Animal@{says=catchPhrase};
}

function createAnimal(catchPhrase: String): Animal
    requires catchPhrase != "";
{
    return Animal@{says=catchPhrase};
}

function createAnimalPreSafe(catchPhrase: String): Animal
    requires#release catchPhrase != "";
{
    return Animal@{says=catchPhrase};
}

entrypoint function getSays(animal: String, catchPhrase: String): Result<String, Any>
    validate animal != "";
    validate catchPhrase != "";
{
    return String::concat("The ", animal, " says ", createAnimal::(catchPhrase).says);
}

createAnimal("woof woof") //ok always
createAnimal("")          //fails invariant in debug
createAnimalPre("")       //fails precondition in debug *but not* release
createAnimalPreSafe("")   //fails precondition in all build flavors

getSays("dog", "woof") //Ok<String, String>{value="The dog says woof"}
getSays("", "woof") //Err<String, String>{error=???}
getSays("dog", "") //Err<String, String>{error=???}
```
## Tooling

**Symbolic Testing**

SymTest is a powerful command line tool for symbolically testing Bosque source code. Details on this symbolic checker can be found in the [readme](./ref_impl/src/runtimes/symtest/README.md).

A sample application for a `division` command line calculator would be to create a file called `division.bsq` with the contents:
```
namespace NSMain;

entrypoint function main(x: Int, y: Int): Int 
    //requires y != 0;
{
    return x / y;
}
```

Then run the following command to check for errors:
```
> node bin\runtimes\symtest\symtest.js division.bsq
```
Which will report that an error is possible.

Re-running the symbolic tested with model generation on as follows:
```
> node bin\runtimes\symtest\symtest.js -m division.bsq
```
Will report that an error is possible when `x == 0` and `y == 0`.

By un-commenting the requires line the tester will assume that the required condition is always satisfied and re-running the tester will now report that the code has been verified up to the bound.

**Ahead-of-Time Compilation**

Bosque supports the generation of standalone command-line executables via the `ExeGen` tool. Details on this tool can be found in the [readme](./ref_impl/src/runtimes/exegen/README.md).

A simple example use is to create a file called "max.bsq" with the following code:
```
namespace NSMain;

entrypoint function main(x: Int, y: Int): Int {
    return (x > y) ? x : y;
}
```
Then run the following command to produce the `max.exe` (on Windows executable) which can then be invoked with:
```
> node ref_impl\bin\runtimes\exegen\exegen.js -o max.exe max.bsq
```
Which will create an executable named `max.exe` in the current directory.

Running this executable:
```
> max.exe 1 5
```
Will output `5`.

## Using the Bosque Language

The current focus of the Bosque project is core language design. As a result there is _no_ support for packaging, deployment, lifecycle management, etc.

### Requirements

In order to build the language the following are needed:

- 64 bit Operating System
- The LTS version of [node.js](https://nodejs.org/en/download/) ( According to your OS )
- Typescript (install with: `npm i typescript -g`)
- A C++ compiler -- by default `clang` on Windows and `g++` on Linux/Mac

### Build & Test

The `ref_impl` directory contains the reference implementation parser, type checker, interpreter, and command line runner. In this directory, build and test the Bosque reference implementation with:

```none
npm install && npm test
```

Note: the Z3 theorem prover is provided as a binary dependency in the repo via git LFS. To ensure these are present you will need to have [git LFS](https://git-lfs.github.com/) installed, run `git lfs install` to setup the needed hooks, and pull. 


### Visual Studio Code Integration

This repository provides basic [Visual Studio Code](https://code.visualstudio.com/) IDE support for the Bosque language (currently limited to syntax and brace highlighting). The installation requires manually copying the full `bosque-language-tools/` folder into your user `.vscode/extensions/` directory and restarting VSCode.

## Contribute

This project welcomes community contributions.

* [Submit bugs](https://github.com/Microsoft/BosqueLanguage/issues) and help us verify fixes.
* [Submit pull requests](https://github.com/Microsoft/BosqueLanguage/pulls) for bug fixes and features and discuss existing proposals.
* Chat about the [@BosqueLanguage](https://twitter.com/BosqueLanguage) (or [#BosqueLanguage](https://twitter.com/hashtag/BosqueLanguage)) on Twitter.

This project has adopted the [Microsoft Open Source Code of Conduct](https://opensource.microsoft.com/codeofconduct/).
For more information see the [Code of Conduct FAQ](https://opensource.microsoft.com/codeofconduct/faq/) or
contact [opencode@microsoft.com](mailto:opencode@microsoft.com) with any additional questions or comments.

Please refer to [Contribution Guidelines](CONTRIBUTING.md) for more details.

## License

Code licensed under the [MIT License](LICENSE.txt).
