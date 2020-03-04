//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as vscode from 'vscode';
import * as Path from 'path';
import { execSync } from 'child_process';

export function activate(context: vscode.ExtensionContext) {
	let tcdisposable = vscode.commands.registerCommand('extension.typecheck', () => {
		const rootws = (vscode.workspace.workspaceFolders || [])[0];
		if(rootws !== undefined) {
			const tcpath = Path.join(__dirname, "../bsqdrop/runtimes/vscmd/vscmd.js");
			const configdir = rootws.uri.fsPath;
			const cmd = `node ${tcpath} typecheck \"${configdir}\"`;

			let oc = vscode.window.createOutputChannel("TypeCheck");
			oc.clear();
			try {
				const outinfo = execSync(cmd).toString();
				const errs = (JSON.parse(outinfo) as Array<string>).map((err) => JSON.parse(err) as [string, number, string]);

				if(errs.length !== 0) {
					const byfile = errs.sort((a, b) => a[0].localeCompare(b[0]));
					const report = byfile.map((err) => `Error in "${err[0]}" on line ${err[1]}: ${err[2]}.`);
					oc.appendLine(report.join("\n"));
					oc.show();
				}
			}
			catch (ex) {
				oc.appendLine(ex.toString());
				oc.show();
			}
		}
	});
	context.subscriptions.push(tcdisposable);

	let vdisposable = vscode.commands.registerCommand('extension.symtest', () => {
		const rootws = (vscode.workspace.workspaceFolders || [])[0];
		if(rootws !== undefined) {
			const tcpath = Path.join(__dirname, "../bsqdrop/runtimes/vscmd/vscmd.js");
			const configdir = rootws.uri.fsPath;
			const cmd = `node ${tcpath} verify \"${configdir}\"`;

			let oc = vscode.window.createOutputChannel("SymbolicTest");
			oc.clear();
			try {
				const outinfo = execSync(cmd).toString();
				oc.appendLine(outinfo);
				oc.show();
			}
			catch (ex) {
				oc.appendLine(ex.toString());
				oc.show();
			}
		}
	});
	context.subscriptions.push(vdisposable);
}

export function deactivate() {}
