# Bosque Programming Language

[![Licensed under the MIT License](https://img.shields.io/badge/License-MIT-blue.svg)](https://github.com/Microsoft/BosqueLanguage/blob/master/LICENSE.txt)
[![PR's Welcome](https://img.shields.io/badge/PRs%20-welcome-brightgreen.svg)](#contribute)
[![Build Status](https://dev.azure.com/bosquepl/BosqueDevOps/_apis/build/status/Microsoft.BosqueLanguage?branchName=master)](https://dev.azure.com/bosquepl/BosqueDevOps/_build/latest?definitionId=1&branchName=master)

The Bosque programming language is a [_Microsoft Research_](https://www.microsoft.com/en-us/research/project/bosque-programming-language/) project on building the development platform for the future of Cloud and IoT application development. The key design features of the language provide ways to avoid _accidental complexity_ in the language, provide semantics that can be easily reasoned about (with automated tools), and in a package that is approachable for developers. The result is improved developer productivity, increased software quality, and a range of new compilers and developer tooling experiences.

Small samples of code to give a sample flavor are below ([Code Snippets](#Code-Snippets)). A rundown of notable and/or unique features in the Bosque language is provided in the [language overview section 0](docs/language/overview.md#0-Highlight-Features).
For a look at how the language works and flows _in the large_ please see the code for a [simple tic-tac-toe](ref_impl/src/test/apps/tictactoe/main.bsq) program that supports updating the board with user supplied moves, making an automated computer move, and managing the various game state.

**Note:** This repository and code represent an alpha state. This means that the language is subject to revision, there are bugs and missing functionality, and the performance is limited. Thus, we **do not** recommend the use of the Bosque language for _any_ production work and instead encourage experimentation only with small/experimental side projects at this point in time.

## News
**Dec 2019**

We have forked off the original v1 version of the language and the master branch is now for the active development of an alpha version!

1. The language semantics have undergone substantial revisions.
2. An Ahead-of-Time compiler is now supported to produce native code (WASM support is planned).
3. A symbolic-tester is provided to augment the use of unit-testing.

## Documentation

* [Language Docs](docs/language/overview.md)
* [Library Docs](docs/libraries/overview.md)
* Tutorials - _Coming Soon!_
* [Technical Papers](docs/papers/publist.md)
* [Contribution guidelines](CONTRIBUTING.md)

## Code Snippets

Add 2 numbers:

```none
function add2(x: Int, y: Int): Int {
    return x + y;
}

add2(2, 3) //5
```

All odd check using rest parameters and lambda:

```none
function allOdd(...args: List<Int>): Bool {
    return args->all(fn(x) => x % 2 == 1);
}

allOdd(1, 3, 4) //false
```

Bulk update properties on Record

```none
function updatePoint(point: {x: Int, y: Int, z: Int}, value: Int): {x: Int, y: Int, z: Int} {
    return point->updatePoint(y=value, x=-point.x);
}

updatePoint({x=1, y=2, z=3}, 5) //{x=-1, y=5, z=3}
```

Noneable access on optional argument:

```none
function tryGetProperty(r?: {f: Int, k: Int}): Int? {
    return r?.f;
}

tryGetProperty({f=2, k=1}) //2
tryGetProperty()           //none
```

Sign (with optional argument):

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

### Command Line Execution

XXXXXX

The `ref_impl` directory contains a simple command line runner for standalone Bosque (`.bsq`) files. These files must have a single `entrypoint` function called `main()` (see [some examples](ref_impl/src/test/apps)). The code in the file can be parsed, type checked, and executed with:

```none
node bin/test/app_runner.js FILE.bsq
```

We also provide a compiler (to bytecode only right now) in the directory `compiler\bcgen.js` and a way to execute the code in the resulting bytecode assemblies with the executor in `interpreter\exec.js`. 

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
