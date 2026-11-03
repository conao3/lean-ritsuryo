module

import Ritsuryo.Cli.Commands
import Ritsuryo.Cli.Render
import Ritsuryo.Cli.Query

/-!
# `ritsuryo` の入口

引数をコマンド表（`Ritsuryo.Cli.commands`）で解析し、バージョン・`help`・雛形を出すか、サブコマンドを実行する。
実行の結果は `--query` の JMESPath で絞り込み、`--output` の形式で標準出力に出す。

終了コードは、0 が成功、252 がコマンドやパラメータの誤り（`--query` の式の誤りを含む）、254 が計算の扱う範囲の外の入力、
255 がそれ以外の失敗（ファイルを読めないなど）になる。誤りは `ritsuryo: error: ...` の形で標準エラーに出す。
-/

open Ritsuryo.Cli

/-- `ritsuryo --version` で出すバージョン。 -/
def version : String := "0.5.0"

/-- 出力の JSON を `--output` の形式の文字列にする。`title` は `table` の題。 -/
def render (fmt : OutputFormat) (title : String) (j : Json) : String :=
  match fmt with
  | .json => Json.pretty j ++ "\n"
  | .text => renderText j
  | .table => renderTable title j

/-- 引数を解析して実行し、終了コードを返す。 -/
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
      -- 名前は parse で確かめてあるので、ここで見つからないことはない。
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
        match g.query with
        | none =>
          IO.print (render g.output (pascalCase sub.name) j)
          return 0
        | some q =>
          match Query.apply q j with
          | .ok j' =>
            IO.print (render g.output (pascalCase sub.name) j')
            return 0
          | .error e =>
            IO.eprintln s!"ritsuryo: error: {e}"
            return 252
      | .error e =>
        IO.eprintln s!"ritsuryo: error: {e.message}"
        return e.code

/-- CLI の入口。`run` の外で起きた例外（ファイルを読めないなど）は終了コード 255 にする。 -/
public def main (argv : List String) : IO UInt32 := do
  try
    run argv
  catch e =>
    IO.eprintln s!"ritsuryo: error: {e}"
    return 255
