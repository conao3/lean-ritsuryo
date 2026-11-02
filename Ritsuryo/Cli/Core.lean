module

public import Ritsuryo.Cli.Json

public section

namespace Ritsuryo.Cli

structure CliError where
  code : UInt32
  message : String

def usageError (message : String) : CliError := ⟨252, message⟩

def domainError (message : String) : CliError := ⟨254, message⟩

def otherError (message : String) : CliError := ⟨255, message⟩

inductive ParamType where
  | date
  | nat
  | flag
  | enum (values : List String)
  | enumList (values : List String)

structure Param where
  name : String
  type : ParamType
  help : String
  required : Bool := false

def pascalCase (kebab : String) : String :=
  String.join ((kebab.splitOn "-").map fun w => w.capitalize)

def Param.key (p : Param) : String :=
  pascalCase p.name

structure Args where
  values : Array (String × Json)

namespace Args

def get? (a : Args) (key : String) : Option Json :=
  (a.values.find? (·.1 == key)).map (·.2)

def str? (a : Args) (key : String) : Option String :=
  match a.get? key with
  | some (.str s) => some s
  | _ => none

def nat? (a : Args) (key : String) : Option Nat :=
  match a.get? key with
  | some (.num n) => some n.toNat
  | _ => none

def flag (a : Args) (key : String) (default : Bool) : Bool :=
  match a.get? key with
  | some (.bool b) => b
  | _ => default

def strs? (a : Args) (key : String) : Option (List String) :=
  match a.get? key with
  | some (.arr xs) => some (xs.toList.filterMap fun | .str s => some s | _ => none)
  | _ => none

end Args

structure Subcommand where
  name : String
  help : String
  params : List Param
  outputSkeleton : Json
  run : Args → Except CliError Json

structure Command where
  name : String
  help : String
  subcommands : List Subcommand

inductive OutputFormat where
  | json
  | text
  | table

inductive Skeleton where
  | input
  | output

structure Globals where
  output : OutputFormat := .json
  debug : Bool := false
  version : Bool := false
  cliInputJson : Option String := none
  skeleton : Option Skeleton := none

inductive Invocation where
  | version
  | help (path : List String)
  | skeleton (cmd : Command) (sub : Subcommand) (kind : Skeleton)
  | run (cmd : Command) (sub : Subcommand) (args : Args)

def typeName : ParamType → String
  | .date => "string (YYYY-MM-DD)"
  | .nat => "integer"
  | .flag => "boolean"
  | .enum vs => "string, one of: " ++ " | ".intercalate vs
  | .enumList vs => "list of strings, each one of: " ++ " | ".intercalate vs

def topHelp (commands : List Command) : String :=
  let lines := commands.map fun c => s!"    {c.name}\n        {c.help}"
  "NAME\n    ritsuryo\n\nDESCRIPTION\n    日本法の期間計算を、Lean 4 で証明した関数で行う。\n\n" ++
    "SYNOPSIS\n    ritsuryo [options] <command> <subcommand> [parameters]\n\n" ++
    "GLOBAL OPTIONS\n    --output (string) json | text | table（既定は json）\n" ++
    "    --debug (boolean) 解析したパラメータを標準エラーに出す\n" ++
    "    --version (boolean) バージョンを出す\n\n" ++
    "AVAILABLE COMMANDS\n" ++ "\n".intercalate lines ++ "\n    help\n"

def commandHelp (c : Command) : String :=
  let lines := c.subcommands.map fun s => s!"    {s.name}\n        {s.help}"
  s!"NAME\n    {c.name}\n\nDESCRIPTION\n    {c.help}\n\n" ++
    s!"SYNOPSIS\n    ritsuryo {c.name} <subcommand> [parameters]\n\n" ++
    "AVAILABLE SUBCOMMANDS\n" ++ "\n".intercalate lines ++ "\n    help\n"

def synopsisOf (p : Param) : String :=
  let value := match p.type with
    | .flag => s!"--{p.name} | --no-{p.name}"
    | .enumList _ => s!"--{p.name} <value> [<value>...]"
    | _ => s!"--{p.name} <value>"
  if p.required then value else s!"[{value}]"

def subcommandHelp (c : Command) (s : Subcommand) : String :=
  let syn := s.params.map fun p => "      " ++ synopsisOf p
  let opts := s.params.map fun p =>
    s!"    --{p.name} ({typeName p.type}){if p.required then " 必須" else ""}\n        {p.help}"
  s!"NAME\n    {s.name}\n\nDESCRIPTION\n    {s.help}\n\n" ++
    s!"SYNOPSIS\n    ritsuryo {c.name} {s.name}\n" ++ "\n".intercalate syn ++
    "\n      [--cli-input-json <value>]\n      [--generate-cli-skeleton <value>]\n\n" ++
    "OPTIONS\n" ++ "\n\n".intercalate opts ++
    "\n\n    --cli-input-json (string)\n        全パラメータを JSON で渡す。" ++
    "キーはパラメータ名の PascalCase。値が file:// で始まるときはファイルを読む。\n\n" ++
    "    --generate-cli-skeleton (string) input | output\n" ++
    "        入力（--cli-input-json の雛形）または出力の雛形を出す。\n\n" ++
    "OUTPUT\n" ++ (Json.pretty s.outputSkeleton) ++ "\n"

def inputSkeleton (s : Subcommand) : Json :=
  .obj (s.params.toArray.map fun p =>
    (p.key, match p.type with
      | .date => .str ""
      | .nat => .num 0
      | .flag => .bool false
      | .enum _ => .str ""
      | .enumList _ => .arr #[.str ""]))

def isDigits (s : String) : Bool :=
  !s.isEmpty && s.all Char.isDigit

def validDateFormat (s : String) : Bool :=
  match s.splitOn "-" with
  | [y, m, d] => y.length == 4 && m.length == 2 && d.length == 2 && isDigits y && isDigits m &&
    isDigits d
  | _ => false

def checkValue (p : Param) (v : Json) : Except CliError Json :=
  let bad (what : String) : Except CliError Json :=
    throw (usageError s!"--{p.name} ({p.key}) には {what} を渡す")
  match p.type, v with
  | .date, .str s => if validDateFormat s then pure v else bad "YYYY-MM-DD 形式の日付"
  | .date, _ => bad "YYYY-MM-DD 形式の日付"
  | .nat, .num n => if n ≥ 0 then pure v else bad "0 以上の整数"
  | .nat, .str s => match s.toNat? with
    | some n => pure (.num n)
    | none => bad "0 以上の整数"
  | .nat, _ => bad "0 以上の整数"
  | .flag, .bool _ => pure v
  | .flag, _ => bad "真偽値"
  | .enum vs, .str s => if vs.contains s then pure v else bad (" | ".intercalate vs ++ " のいずれか")
  | .enum vs, _ => bad (" | ".intercalate vs ++ " のいずれか")
  | .enumList vs, .arr xs =>
    if xs.all fun | .str s => vs.contains s | _ => false then pure v
    else bad (" | ".intercalate vs ++ " の並び")
  | .enumList vs, _ => bad (" | ".intercalate vs ++ " の並び")

def readValue (raw : String) : IO String := do
  if raw.startsWith "file://" then
    let path := (raw.drop 7).toString
    try
      let content ← IO.FS.readFile path
      return content.trimAsciiEnd.toString
    catch e =>
      throw (IO.userError s!"{path} を読めない: {e}")
  else return raw

def fromCli (p : Param) (values : List String) : IO (Except CliError Json) := do
  match p.type with
  | .flag =>
    if values.isEmpty then return .ok (.bool true)
    else return .error (usageError s!"--{p.name} は値を取らない")
  | .enumList _ =>
    match values with
    | [] => return .error (usageError s!"--{p.name} に値がない")
    | [single] =>
      if single.startsWith "file://" then
        let content ← readValue single
        match Json.parse content with
        | .ok j => return checkValue p j
        | .error e => return .error (usageError s!"--{p.name} の JSON を解析できない: {e}")
      else return checkValue p (.arr #[.str single])
    | vs => return checkValue p (.arr (vs.toArray.map .str))
  | _ =>
    match values with
    | [v] => return checkValue p (.str (← readValue v))
    | [] => return .error (usageError s!"--{p.name} に値がない")
    | _ => return .error (usageError s!"--{p.name} は値を 1 つだけ取る")

structure RawArgs where
  globals : Globals := {}
  positionals : Array String := #[]
  params : Array (String × List String) := #[]

def isOption (s : String) : Bool :=
  s.startsWith "--"

partial def scan (args : List String) (acc : RawArgs) : Except CliError RawArgs :=
  match args with
  | [] => .ok acc
  | "--output" :: v :: rest =>
    let fmt := match v with
      | "json" => some OutputFormat.json
      | "text" => some .text
      | "table" => some .table
      | _ => none
    match fmt with
    | some f => scan rest { acc with globals := { acc.globals with output := f } }
    | none => .error (usageError s!"--output には json | text | table を渡す（{v} は使えない）")
  | ["--output"] => .error (usageError "--output に値がない")
  | "--debug" :: rest => scan rest { acc with globals := { acc.globals with debug := true } }
  | "--version" :: rest => scan rest { acc with globals := { acc.globals with version := true } }
  | "--cli-input-json" :: v :: rest =>
    scan rest { acc with globals := { acc.globals with cliInputJson := some v } }
  | ["--cli-input-json"] => .error (usageError "--cli-input-json に値がない")
  | "--generate-cli-skeleton" :: rest =>
    match rest with
    | "input" :: rest' =>
      scan rest' { acc with globals := { acc.globals with skeleton := some .input } }
    | "output" :: rest' =>
      scan rest' { acc with globals := { acc.globals with skeleton := some .output } }
    | _ => scan rest { acc with globals := { acc.globals with skeleton := some .input } }
  | a :: rest =>
    if isOption a then
      let values := rest.takeWhile (!isOption ·)
      let param := ((a.drop 2).toString, values)
      scan (rest.drop values.length) { acc with params := acc.params.push param }
    else scan rest { acc with positionals := acc.positionals.push a }

def bindParams (s : Subcommand) (raw : RawArgs) : IO (Except CliError Args) := do
  let mut values : Array (String × Json) := #[]
  if let some src := raw.globals.cliInputJson then
    let text ← readValue src
    match Json.parse text with
    | .error e => return .error (usageError s!"--cli-input-json の JSON を解析できない: {e}")
    | .ok (.obj fields) =>
      for (k, v) in fields do
        match s.params.find? (·.key == k) with
        | none => return .error (usageError s!"--cli-input-json のキー {k} は {s.name} のパラメータではない")
        | some p =>
          match checkValue p v with
          | .ok v' => values := values.push (k, v')
          | .error e => return .error e
    | .ok _ => return .error (usageError "--cli-input-json には JSON のオブジェクトを渡す")
  for (name, vs) in raw.params do
    let (p?, negated) : Option Param × Bool :=
      match s.params.find? (·.name == name) with
      | some p => (some p, false)
      | none =>
        if name.startsWith "no-" then
          match s.params.find? (fun (p : Param) => p.name == (name.drop 3).toString) with
          | some p => match p.type with
            | .flag => (some p, true)
            | _ => (none, false)
          | none => (none, false)
        else (none, false)
    match p? with
    | none => return .error (usageError s!"--{name} は {s.name} のパラメータではない")
    | some p =>
      let v : Except CliError Json ← if negated then
          pure (if vs.isEmpty then Except.ok (Json.bool false)
            else Except.error (usageError s!"--no-{p.name} は値を取らない"))
        else fromCli p vs
      match v with
      | .ok v' => values := (values.filter (·.1 != p.key)).push (p.key, v')
      | .error e => return .error e
  for p in s.params do
    if p.required && !(values.any (·.1 == p.key)) then
      return .error (usageError s!"--{p.name} は必須")
  return .ok ⟨values⟩

def parse (commands : List Command) (argv : List String) :
    IO (Except CliError (Globals × Invocation)) := do
  match scan argv {} with
  | .error e => return .error e
  | .ok raw =>
    let g := raw.globals
    match raw.positionals.toList with
    | [] =>
      if g.version then return .ok (g, .version)
      else return .error (usageError "コマンドがない。ritsuryo help で一覧を出す")
    | ["help"] => return .ok (g, .help [])
    | c :: rest =>
      match commands.find? (·.name == c) with
      | none => return .error (usageError s!"コマンド {c} はない。ritsuryo help で一覧を出す")
      | some cmd =>
        match rest with
        | [] => return .error (usageError s!"サブコマンドがない。ritsuryo {c} help で一覧を出す")
        | ["help"] => return .ok (g, .help [c])
        | s :: rest' =>
          match cmd.subcommands.find? (·.name == s) with
          | none =>
            return .error (usageError s!"サブコマンド {s} はない。ritsuryo {c} help で一覧を出す")
          | some sub =>
            match rest' with
            | ["help"] => return .ok (g, .help [c, s])
            | [] =>
              if let some k := g.skeleton then return .ok (g, .skeleton cmd sub k)
              match ← bindParams sub raw with
              | .ok args => return .ok (g, .run cmd sub args)
              | .error e => return .error e
            | extra :: _ => return .error (usageError s!"位置引数 {extra} は受け付けない")

end Ritsuryo.Cli
