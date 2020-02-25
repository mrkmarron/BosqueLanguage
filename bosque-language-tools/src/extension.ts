//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as vscode from 'vscode';

import * as FS from "fs";
import * as Path from "path";

function typecheck(files: string[], corelibpath: string): string[] {
    let code: { relativePath: string, contents: string }[] = [];
    try {
        const coredir = Path.join(corelibpath, "/core.bsq");
        const coredata = FS.readFileSync(coredir).toString();

        const collectionsdir = Path.join(corelibpath, "/collections.bsq");
        const collectionsdata = FS.readFileSync(collectionsdir).toString();

        code = [{ relativePath: coredir, contents: coredata }, { relativePath: collectionsdir, contents: collectionsdata }];
        for (let i = 0; i < files.length; ++i) {
            const file = { relativePath: files[i], contents: FS.readFileSync(files[i]).toString() };
            code.push(file);
        }
    }
    catch (ex) {
        process.stdout.write(`Read failed with exception -- ${ex}\n`);
        process.exit(1);
    }

    return MIREmitter.generateMASM(new PackageConfig(), "debug", true, code)[1]; 
}

export function activate(context: vscode.ExtensionContext) {
	let disposable = vscode.commands.registerCommand('extension.typecheck', () => {
		// The code you place here will be executed every time your command is executed

		// Display a message box to the user
		vscode.window.showInformationMessage('Hello World!');
	});

	context.subscriptions.push(disposable);
}

export function deactivate() {}
