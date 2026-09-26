namespace Clef.Compiler.Service.Tests

open System
open Xunit
open Clef.Compiler.Syntax
open Clef.Compiler.NativeService

/// Syntax contracts only. These tests do not establish runtime demand semantics.
module private EagerSyntax =
    let bindings source =
        match parseStringWithDefaults source "eager-syntax.clef" with
        | ParseSuccess (ParsedInput.ImplFile implementation) ->
            let (SynModuleOrNamespace(decls = declarations)) = Assert.Single implementation.Contents
            declarations
            |> List.collect (function SynModuleDecl.Let(bindings = values) -> values | _ -> [])
        | result -> failwithf "Expected parsed implementation: %A" result

    let expression text =
        let binding = bindings ("module EagerSyntax\nlet target = " + text + "\n") |> Assert.Single
        let (SynBinding(expr = result)) = binding
        result

    let rec strip = function
        | SynExpr.Paren(expr = inner)
        | SynExpr.Typed(expr = inner) -> strip inner
        | expression -> expression

    let rec shape expression =
        match strip expression with
        | SynExpr.Ident identifier -> identifier.idText
        | SynExpr.LongIdent(longDotId = identifier) -> identifier.LongIdent |> List.map _.idText |> String.concat "."
        | SynExpr.Const(SynConst.Int32 value, _) -> string value
        | SynExpr.Const(SynConst.Bool value, _) -> if value then "true" else "false"
        | SynExpr.Const(SynConst.Unit, _) -> "unit"
        | SynExpr.App(funcExpr = fn; argExpr = argument) -> "app(" + shape fn + "," + shape argument + ")"
        | SynExpr.Eager(expr = inner) -> "eager(" + shape inner + ")"
        | SynExpr.Lazy(expr = inner) -> "lazy(" + shape inner + ")"
        | SynExpr.Lambda(body = body) -> "lambda(" + shape body + ")"
        | SynExpr.IfThenElse(ifExpr = condition; thenExpr = yes; elseExpr = Some no) ->
            "if(" + shape condition + "," + shape yes + "," + shape no + ")"
        | SynExpr.Tuple(exprs = values) -> "tuple(" + (values |> List.map shape |> String.concat ",") + ")"
        | SynExpr.ArrayOrList(isArray = array; exprs = values) ->
            (if array then "array(" else "list(") + (values |> List.map shape |> String.concat ",") + ")"
        | SynExpr.ArrayOrListComputed(isArray = array; expr = body) ->
            (if array then "array(" else "list(") + shape body + ")"
        | SynExpr.Sequential(expr1 = first; expr2 = second) -> shape first + "," + shape second
        | SynExpr.Record(recordFields = fields) ->
            let values = fields |> List.map (fun (SynExprRecordField(expr = value)) -> value.Value)
            "record(" + (values |> List.map shape |> String.concat ",") + ")"
        | other -> failwithf "Unexpected syntax in boundary fixture: %A" other

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "EagerSyntax")>]
type EagerSyntaxCases() =
    [<Theory>]
    [<InlineData("eager transform 1", "eager(app(transform,1))")>]
    [<InlineData("eager transform 1 2", "eager(app(app(transform,1),2))")>]
    [<InlineData("(eager transform) 1", "app(eager(transform),1)")>]
    [<InlineData("eager transform 1 + 2", "app(app(op_Addition,eager(app(transform,1))),2)")>]
    [<InlineData("(eager transform 1) + 2", "app(app(op_Addition,eager(app(transform,1))),2)")>]
    [<InlineData("eager (transform 1 + 2)", "eager(app(app(op_Addition,app(transform,1)),2))")>]
    [<InlineData("lazy transform 1 + 2", "app(app(op_Addition,lazy(app(transform,1))),2)")>]
    member _.``Eager operand extent follows lazy prefix precedence``(source, expected) =
        Assert.Equal(expected, EagerSyntax.shape (EagerSyntax.expression source))

    [<Theory>]
    [<InlineData("lazy (eager work())", "lazy(eager(app(work,unit)))")>]
    [<InlineData("eager (lazy work())", "eager(lazy(app(work,unit)))")>]
    [<InlineData("fun value -> eager work value", "lambda(eager(app(work,value)))")>]
    [<InlineData("eager (fun value -> work value)", "eager(lambda(app(work,value)))")>]
    [<InlineData("if choice then eager work 1 else work 2", "if(choice,eager(app(work,1)),app(work,2))")>]
    [<InlineData("eager (if choice then work 1 else work 2)", "eager(if(choice,app(work,1),app(work,2)))")>]
    member _.``Enclosing deferred and selected expression boundaries remain in syntax``(source, expected) =
        Assert.Equal(expected, EagerSyntax.shape (EagerSyntax.expression source))

    [<Theory>]
    [<InlineData("consume (eager work 1) deferred", "app(app(consume,eager(app(work,1))),deferred)")>]
    [<InlineData("consume (eager work 1)", "app(consume,eager(app(work,1)))")>]
    [<InlineData("consume (nested (eager work 1))", "app(consume,app(nested,eager(app(work,1))))")>]
    [<InlineData("((eager work 1) : int)", "eager(app(work,1))")>]
    [<InlineData("begin eager work 1 end", "eager(app(work,1))")>]
    [<InlineData("(eager work 1, deferred)", "tuple(eager(app(work,1)),deferred)")>]
    [<InlineData("{ First = eager work 1; Second = deferred }", "record(eager(app(work,1)),deferred)")>]
    [<InlineData("Some (eager work 1)", "app(Some,eager(app(work,1)))")>]
    [<InlineData("[| eager work 1; deferred |]", "array(eager(app(work,1)),deferred)")>]
    [<InlineData("[ eager work 1; deferred ]", "list(eager(app(work,1)),deferred)")>]
    member _.``Direct actuals components and transparent wrappers retain marker position``(source, expected) =
        Assert.Equal(expected, EagerSyntax.shape (EagerSyntax.expression source))

    [<Fact>]
    member _.``Marker and operand ranges cover their original source independently``() =
        let source = "eager transform 123"
        match EagerSyntax.expression source with
        | SynExpr.Eager(expr = operand; range = markerRange) ->
            Assert.Equal(2, markerRange.StartLine)
            Assert.Equal(13, markerRange.StartColumn)
            Assert.Equal(13 + source.Length, markerRange.EndColumn)
            Assert.Equal(2, operand.Range.StartLine)
            Assert.Equal(19, operand.Range.StartColumn)
            Assert.Equal(markerRange.EndColumn, operand.Range.EndColumn)
        | other -> failwithf "Lost eager source marker: %A" other

    [<Fact>]
    member _.``Multiline eager block respects offside and following binding``() =
        let source = "module EagerSyntax\nlet target =\n    eager\n        let local = transform 1\n        local\nlet after = 2\n"
        let bindings = EagerSyntax.bindings source
        Assert.Equal(2, bindings.Length)
        let (SynBinding(expr = target)) = bindings[0]
        match target with
        | SynExpr.Eager(expr = SynExpr.LetOrUse binding; range = markerRange) ->
            Assert.Equal("local", EagerSyntax.shape binding.Body)
            Assert.Equal(3, markerRange.StartLine)
            Assert.Equal(5, markerRange.EndLine)
        | other -> failwithf "Lost multiline eager block: %A" other
        let (SynBinding(expr = after)) = bindings[1]
        Assert.Equal("2", EagerSyntax.shape after)

    [<Theory>]
    [<InlineData("module EagerSyntax\nlet eager = 1\n")>]
    [<InlineData("module EagerSyntax\nlet target = fun eager -> eager\n")>]
    [<InlineData("module EagerSyntax\nlet target = eager\n")>]
    member _.``Eager is a keyword and requires its operand``(source) =
        match parseStringWithDefaults source "invalid-eager.clef" with
        | ParseError errors -> Assert.NotEmpty errors
        | result -> failwithf "Malformed or unquoted eager identifier parsed: %A" result

    [<Fact>]
    member _.``Quoted eager remains a normal binding and value identifier``() =
        let parsed = EagerSyntax.bindings "module EagerSyntax\nlet ``eager`` = 1\nlet target = ``eager``\n"
        Assert.Equal(2, parsed.Length)
        let (SynBinding(expr = first)) = parsed[0]
        let (SynBinding(expr = reference)) = parsed[1]
        Assert.Equal("1", EagerSyntax.shape first)
        match reference with
        | SynExpr.Ident identifier -> Assert.Equal("eager", identifier.idText)
        | other -> failwithf "Quoted identifier became a demand marker: %A" other
