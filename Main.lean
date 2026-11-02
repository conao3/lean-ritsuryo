module

import Ritsuryo.Cli.Commands
import Ritsuryo.Cli.Render

open Ritsuryo.Cli

def version : String := "0.1.0"

def render (fmt : OutputFormat) (title : String) (j : Json) : String :=
  match fmt with
  | .json => Json.pretty j ++ "\n"
  | .text => renderText j
  | .table => renderTable title j

def run (argv : List String) : IO UInt32 := do
  match ← parse commands argv with
  | .error e =>
    IO.eprintln s!"ritsuryo: error: {e.message}"
    return e.code
  | .ok (g, inv) =>
    match inv with
    | .version =>
      IO.println s!"ritsuryo {version}"
      return 0
    | .help [] =>
      IO.print (topHelp commands)
      return 0
    | .help (c :: rest) =>
      match commands.find? (·.name == c) with
      | none => return 252
      | some cmd =>
        match rest with
        | [] => IO.print (commandHelp cmd)
        | s :: _ =>
          match cmd.subcommands.find? (·.name == s) with
          | some sub => IO.print (subcommandHelp cmd sub)
          | none => return 252
        return 0
    | .skeleton _ sub kind =>
      let j := match kind with
        | .input => inputSkeleton sub
        | .output => sub.outputSkeleton
      IO.println (Json.pretty j)
      return 0
    | .run _ sub args =>
      if g.debug then
        IO.eprintln (Json.pretty (.obj args.values))
      match sub.run args with
      | .ok j =>
        IO.print (render g.output (pascalCase sub.name) j)
        return 0
      | .error e =>
        IO.eprintln s!"ritsuryo: error: {e.message}"
        return e.code

public def main (argv : List String) : IO UInt32 := do
  try
    run argv
  catch e =>
    IO.eprintln s!"ritsuryo: error: {e}"
    return 255
