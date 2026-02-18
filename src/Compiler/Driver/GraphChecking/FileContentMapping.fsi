module internal rec Clef.Compiler.GraphChecking.FileContentMapping

/// Extract the FileContentEntries from the ParsedInput of a file.
val mkFileContent: f: FileInProject -> FileContentEntry list
