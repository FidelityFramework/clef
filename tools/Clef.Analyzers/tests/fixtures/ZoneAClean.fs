// Positive control: pure algebraic Zone A code.  The analyzer must report no
// AXC/CLF diagnostic for this file (AXD000 is still emitted).
// Also tests clean lookalikes inside strings, single-$ interpolated literals,
// and nested block comments containing quoted strings:
// (* "*)" (* nested null %A %O (# "throw" $$""" *) *)
module ClefAnalyzerZoneAClean

type Cell = { Id : int; Value : int }

let sumCells (cells : Cell list) : int =
    cells |> List.fold (fun total cell -> total + cell.Value) 0

let pairCells (cells : Cell list) : (Cell * Cell) list =
    cells |> List.pairwise

let labelOf (cell : Cell) : string =
    sprintf "cell %d %%A $$ null // literal" cell.Id

let interpolatedLiteral (cell : Cell) : string =
    $"""literal null and {{braces}} id={cell.Id}"""

let lengthOf (values : int array) : int =
    values.Length

(* "string with *)" inside block comment must not terminate comment early *)
let genericIdentity<'T> (value : 'T) : 'T =
    // Type parameter 'T must not confuse the char-literal lexer.
    value
