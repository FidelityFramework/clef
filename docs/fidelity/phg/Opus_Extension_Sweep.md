# The extension sweep: `.fs` to `.clef` in the compiler sources

> A mechanical brief for an agent that makes no structural decisions. It renames every F# source file of the CCS and Composer repositories from `.fs` to `.clef`, rewrites the project files to match, and re-runs every gate that passes today. That is the whole task. Anything not written here is not part of it, and any decision the steps below do not make is the owner's: stop and ask.

## 0. Before anything: the build must accept the extension

On 2026-09-05 the stock F# compiler shipped with the .NET SDK on this machine refuses a `.clef` source file:

```
error FS0226: The file extension of 'A.clef' is not recognized. Source files must have extension .fs, .fsi, .fsx or .fsscript
```

Both repositories are built by that compiler (`dotnet build` of `Clef.Compiler.Service.fsproj` and `Composer.fsproj`; neither `Directory.Build.props` names another compiler), and the CCS fork does not ship as a command-line compiler. So the rename cannot build until the owner has put an enabling mechanism in place and named it in this section. Until this section names one, **stop at step 1**: run the probe, report its result, and do nothing else.

The probe (run it exactly; it touches no repository):

```
mkdir -p /tmp/extprobe && cd /tmp/extprobe
printf 'module M\nlet x = 1\n' > A.clef
printf '<Project Sdk="Microsoft.NET.Sdk">\n<PropertyGroup><OutputType>Library</OutputType><TargetFramework>net10.0</TargetFramework></PropertyGroup>\n<ItemGroup><Compile Include="A.clef" /></ItemGroup>\n</Project>\n' > P.fsproj
dotnet build P.fsproj
```

Enabling mechanism, as the owner rules it: _(unset; the owner writes one line here, and the exact property or file that carries it, before this sweep may proceed)_.

## 1. Scope, exactly

- `/home/hhh/repos/clef/src/Compiler/**/*.fs` and `/home/hhh/repos/Composer/src/**/*.fs`, and only files listed in a `<Compile Include=...>` of a `.fsproj` under those two roots. Nothing under `bin/`, `obj/`, `tests/`, `samples/`, `docs/`, or any other repository.
- `.fsi`, `.fsx`, `.fsl`, `.fsy`, `.resx`, `.txt` and every other extension: untouched.
- No file content changes of any kind. No reformatting, no comment edits, no reordering, no "while I'm here". A diff that shows anything but renames and `Compile Include` path rewrites is a failed run.

## 2. Steps

1. Run the §0 probe. If it fails, stop and report the output verbatim.
2. Inventory: for each of the two roots, list every `<Compile Include="…\.fs" />` (and `Include="…/….fs"`) across all `.fsproj` files, and every `*.fs` on disk under the root. Report both counts and any file on disk that no project lists, or listed but absent. Do not rename an unlisted file.
3. Rename with history: `git mv path/File.fs path/File.clef` for every listed file, one repository at a time.
4. Rewrite each `.fsproj`: every `Compile Include` that ended in `.fs` now ends in `.clef`, path otherwise unchanged. Nothing else in the project file changes.
5. Build both, in this order: `dotnet build /home/hhh/repos/clef/src/Compiler/Clef.Compiler.Service.fsproj`, then `dotnet build /home/hhh/repos/Composer/src/Composer.fsproj`. Both clean, or stop and report the first error verbatim.
6. Run every gate in `Dimensional_Handoff.md` §5 and record each result. Every result must equal the recorded value (transcript identical, `25 HDL ports`, `23 unsat`, `309 passed, 0 failed`, the harness count and every judged row `ok`, the placement checks). A single difference is a stop and a report; do not "fix" anything.
7. Report: the two inventories, the two build results, the gate table filled in, and `git status --short` of both repositories. Propose one commit line per repository, `chore(<scope>): source files renamed .fs to .clef`. Do not commit.

## 3. What this agent does not do

It does not touch file contents. It does not rename tests, samples, scripts or documents. It does not change build properties, targets or SDK versions. It does not decide how the extension is enabled. It does not continue past a failed probe, a failed build, or a changed gate. It does not open, summarise or reinterpret the design documents; it follows this brief.
