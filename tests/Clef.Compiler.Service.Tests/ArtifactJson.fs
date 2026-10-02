namespace Clef.Compiler.Service.Tests

open Fidelity.Data.JSON

/// Strict assertions over the compiler's explicit diagnostic JSON schemas.
module ArtifactJson =
    let parse text = Json.parse text |> Result.defaultWith failwith
    let field name value =
        JsonValue.prop name value |> Option.defaultWith (fun () -> failwithf "Missing JSON field '%s'" name)
    let text value =
        JsonValue.asString value |> Option.defaultWith (fun () -> failwith "Expected JSON string")
    let integer value =
        match JsonValue.tryAsInt64 value with
        | Some integer when integer >= -2147483648L && integer <= 2147483647L -> int integer
        | _ -> failwith "Expected exact JSON int32"
    let boolean value =
        JsonValue.asBool value |> Option.defaultWith (fun () -> failwith "Expected JSON boolean")
    let items = function
        | JsonValue.Array values -> values
        | _ -> failwith "Expected JSON array"
    let count value = items value |> List.length
    let at index value = items value |> List.item index
