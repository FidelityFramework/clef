module internal Clef.Compiler.Utilities.LinuxHostTools

open System.Runtime.InteropServices

[<DllImport("libc", EntryPoint="access", SetLastError=true)>]
extern int access(string path, int mode)

let canExecute path = access(path,1)=0
