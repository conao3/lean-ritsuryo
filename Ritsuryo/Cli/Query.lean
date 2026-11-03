module

public import Ritsuryo.Cli.Json

/-!
# `--query`（JMESPath）

AWS CLI と同じく、出力の JSON を JMESPath（https://jmespath.org/specification.html）の式で絞り込む。
Lean には JMESPath の実装がないので、仕様の構文の多くを自前で書く。

扱う構文: 識別子（`Result`、`"Quoted Key"`）、サブ式（`a.b`）、添字（`[0]`、`[-1]`）、スライス（`[1:3]`）、
リストの射影（`[*]`）、オブジェクトの射影（`*`）、平坦化（`[]`）、フィルタ（`[?Rate=='standard']`）、
複数選択（`[a, b]`、`{A: a, B: b}`）、パイプ（`|`）、比較（`==` `!=` `<` `<=` `>` `>=`）、
論理演算（`||` `&&` `!`）、括弧、`@`、リテラル（`` `1` ``、`'raw'`）、関数
（`length` `keys` `values` `sort` `reverse` `max` `min` `sum` `join` `contains` `starts_with`
`ends_with` `type` `to_string` `not_null`）。

構文解析は jmespath.py と同じ Pratt 法（演算子ごとの結合の強さ `bp` で木を組む）による。
-/

public section

namespace Ritsuryo.Cli.Query

/-- 字句。 -/
inductive Token where
  | ident (s : String)
  | quoted (s : String)
  | literal (j : Json)
  | number (n : Int)
  | dot | star | comma | colon | pipe | or | and | not
  | lbracket | rbracket | lbrace | rbrace | lparen | rparen
  | filter | flatten | current
  | cmp (op : String)
  | eof
  deriving Inhabited

/-- 式の木。 -/
inductive Ast where
  | current
  | field (name : String)
  | literal (j : Json)
  | sub (lhs rhs : Ast)
  | index (i : Int)
  | slice (start stop : Option Int)
  /-- リストの射影。`lhs` を評価した配列の各要素に `rhs` を当て、null を除く -/
  | project (lhs rhs : Ast)
  /-- オブジェクトの値の射影 -/
  | valueProject (lhs rhs : Ast)
  | flatten (lhs : Ast)
  | filterProject (lhs cond rhs : Ast)
  | pipe (lhs rhs : Ast)
  | or (lhs rhs : Ast)
  | and (lhs rhs : Ast)
  | not (e : Ast)
  | cmp (op : String) (lhs rhs : Ast)
  | multiList (xs : List Ast)
  | multiHash (xs : List (String × Ast))
  | call (name : String) (args : List Ast)
  deriving Inhabited

def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_'

def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_'

/-- 字句解析。 -/
partial def tokenize (s : String) : Except String (Array Token) :=
  let cs := s.toList.toArray
  let rec go (i : Nat) (acc : Array Token) : Except String (Array Token) :=
    match cs[i]? with
    | none => .ok (acc.push .eof)
    | some c =>
      let next := cs[i + 1]?
      if c == ' ' || c == '\t' || c == '\n' then go (i + 1) acc
      else if isIdentStart c then
        let j := (List.range (cs.size - i)).find? (fun k => !isIdentChar (cs[i + k]!))
          |>.getD (cs.size - i)
        go (i + j) (acc.push (.ident (String.ofList (cs.extract i (i + j)).toList)))
      else if c.isDigit || (c == '-' && (next.map Char.isDigit).getD false) then
        let start := if c == '-' then i + 1 else i
        let j := (List.range (cs.size - start)).find? (fun k => !(cs[start + k]!).isDigit)
          |>.getD (cs.size - start)
        let n := (String.ofList (cs.extract start (start + j)).toList).toNat!
        go (start + j) (acc.push (.number (if c == '-' then -(n : Int) else n)))
      else if c == '"' then
        let rec str (k : Nat) (out : String) : Except String (Nat × String) :=
          match cs[k]? with
          | none => .error "引用符で囲んだ識別子が閉じていない"
          | some '"' => .ok (k + 1, out)
          | some '\\' => match cs[k + 1]? with
            | some d => str (k + 2) (out.push d)
            | none => .error "引用符で囲んだ識別子が閉じていない"
          | some d => str (k + 1) (out.push d)
        match str (i + 1) "" with
        | .ok (k, out) => go k (acc.push (.quoted out))
        | .error e => .error e
      else if c == '\'' then
        let rec raw (k : Nat) (out : String) : Except String (Nat × String) :=
          match cs[k]? with
          | none => .error "生の文字列リテラルが閉じていない"
          | some '\'' => .ok (k + 1, out)
          | some '\\' => match cs[k + 1]? with
            | some '\'' => raw (k + 2) (out.push '\'')
            | _ => raw (k + 1) (out.push '\\')
          | some d => raw (k + 1) (out.push d)
        match raw (i + 1) "" with
        | .ok (k, out) => go k (acc.push (.literal (.str out)))
        | .error e => .error e
      else if c == '`' then
        let j := (List.range (cs.size - i - 1)).find? (fun k => cs[i + 1 + k]! == '`')
        match j with
        | none => .error "JSON リテラルが閉じていない"
        | some j =>
          let body := String.ofList (cs.extract (i + 1) (i + 1 + j)).toList
          match Json.parse body with
          | .ok v => go (i + j + 2) (acc.push (.literal v))
          | .error _ => go (i + j + 2) (acc.push (.literal (.str body.trimAscii.toString)))
      else
        match c, next with
        | '[', some '?' => go (i + 2) (acc.push .filter)
        | '[', some ']' => go (i + 2) (acc.push .flatten)
        | '|', some '|' => go (i + 2) (acc.push .or)
        | '&', some '&' => go (i + 2) (acc.push .and)
        | '=', some '=' => go (i + 2) (acc.push (.cmp "=="))
        | '!', some '=' => go (i + 2) (acc.push (.cmp "!="))
        | '<', some '=' => go (i + 2) (acc.push (.cmp "<="))
        | '>', some '=' => go (i + 2) (acc.push (.cmp ">="))
        | '<', _ => go (i + 1) (acc.push (.cmp "<"))
        | '>', _ => go (i + 1) (acc.push (.cmp ">"))
        | '!', _ => go (i + 1) (acc.push .not)
        | '.', _ => go (i + 1) (acc.push .dot)
        | '*', _ => go (i + 1) (acc.push .star)
        | ',', _ => go (i + 1) (acc.push .comma)
        | ':', _ => go (i + 1) (acc.push .colon)
        | '|', _ => go (i + 1) (acc.push .pipe)
        | '[', _ => go (i + 1) (acc.push .lbracket)
        | ']', _ => go (i + 1) (acc.push .rbracket)
        | '{', _ => go (i + 1) (acc.push .lbrace)
        | '}', _ => go (i + 1) (acc.push .rbrace)
        | '(', _ => go (i + 1) (acc.push .lparen)
        | ')', _ => go (i + 1) (acc.push .rparen)
        | '@', _ => go (i + 1) (acc.push .current)
        | _, _ => .error s!"--query に使えない文字 '{c}' がある"
  go 0 #[]

/-- 結合の強さ（jmespath.py の binding_power と同じ値）。 -/
def bp : Token → Nat
  | .pipe => 1
  | .or => 2
  | .and => 3
  | .cmp _ => 5
  | .flatten => 9
  | .star => 20
  | .filter => 21
  | .dot => 40
  | .not => 45
  | .lbrace => 50
  | .lbracket => 55
  | .lparen => 60
  | _ => 0

structure PState where
  tokens : Array Token
  pos : Nat

abbrev PM := StateT PState (Except String)

def peekTok : PM Token := do
  let s ← get
  return s.tokens[s.pos]?.getD .eof

def peekTok2 : PM Token := do
  let s ← get
  return s.tokens[s.pos + 1]?.getD .eof

def nextTok : PM Token := do
  let t ← peekTok
  modify fun s => { s with pos := s.pos + 1 }
  return t

def expectTok (name : String) (ok : Token → Bool) : PM Unit := do
  let t ← nextTok
  if !ok t then throw s!"--query の構文: {name} がない"

mutual

/-- `rbp` より強く結合する演算子を取り込みながら式を読む。 -/
partial def expr (rbp : Nat) : PM Ast := do
  let t ← nextTok
  let mut left ← nud t
  repeat
    let t ← peekTok
    if rbp < bp t then
      let _ ← nextTok
      left ← led t left
    else break
  return left

partial def nud : Token → PM Ast
  | .ident s => return .field s
  | .quoted s => return .field s
  | .literal j => return .literal j
  | .current => return .current
  | .not => return .not (← expr (bp .not))
  | .lparen => do
    let e ← expr 0
    expectTok "')'" fun | .rparen => true | _ => false
    return e
  | .star => return .valueProject .current (← projectionRhs (bp .star))
  | .flatten => return .project (.flatten .current) (← projectionRhs (bp .flatten))
  | .filter => filterTail .current
  | .lbrace => multiHash
  | .lbracket => do
    match ← peekTok with
    | .number _ | .colon => bracketIndex .current
    | .star =>
      if let .rbracket ← peekTok2 then
        let _ ← nextTok
        let _ ← nextTok
        return .project .current (← projectionRhs (bp .star))
      else multiList
    | _ => multiList
  | .eof => throw "--query が途中で終わっている"
  | _ => throw "--query の構文: 式の始まりに置けない記号がある"

partial def led (t : Token) (left : Ast) : PM Ast :=
  match t with
  | .dot => do
    if let .star ← peekTok then
      let _ ← nextTok
      return .valueProject left (← projectionRhs (bp .star))
    return .sub left (← dotRhs (bp .dot))
  | .pipe => return .pipe left (← expr (bp .pipe))
  | .or => return .or left (← expr (bp .or))
  | .and => return .and left (← expr (bp .and))
  | .cmp op => return .cmp op left (← expr (bp t))
  | .flatten => return .project (.flatten left) (← projectionRhs (bp .flatten))
  | .filter => filterTail left
  | .lparen => do
    let .field name := left | throw "--query の構文: 関数名がない"
    let mut args : List Ast := []
    if let .rparen ← peekTok then
      let _ ← nextTok
      return .call name []
    repeat
      args := args ++ [← expr 0]
      match ← nextTok with
      | .comma => continue
      | .rparen => break
      | _ => throw "--query の構文: 関数の引数の後に ',' か ')' がない"
    return .call name args
  | .lbracket => do
    match ← peekTok with
    | .number _ | .colon => bracketIndex left
    | .star =>
      let _ ← nextTok
      expectTok "']'" fun | .rbracket => true | _ => false
      return .project left (← projectionRhs (bp .star))
    | _ => throw "--query の構文: '[' の後に添字か '*' がない"
  | _ => throw "--query の構文: 演算子の位置がおかしい"

/-- `[` の後の添字かスライス。スライスは射影になる。 -/
partial def bracketIndex (left : Ast) : PM Ast := do
  let num : PM (Option Int) := do
    match ← peekTok with
    | .number n => let _ ← nextTok; return some n
    | _ => return none
  let a ← num
  match ← nextTok with
  | .rbracket =>
    let some i := a | throw "--query の構文: 添字がない"
    return .sub left (.index i)
  | .colon =>
    let b ← num
    expectTok "']'" fun | .rbracket => true | _ => false
    return .project (.sub left (.slice a b)) (← projectionRhs (bp .star))
  | _ => throw "--query の構文: 添字の後に ']' がない"

partial def filterTail (left : Ast) : PM Ast := do
  let cond ← expr 0
  expectTok "']'" fun | .rbracket => true | _ => false
  return .filterProject left cond (← projectionRhs (bp .filter))

/-- 射影の右側。続く演算子が弱ければ何もしない（`@`）。 -/
partial def projectionRhs (rbp : Nat) : PM Ast := do
  let t ← peekTok
  if bp t < 10 then return .current
  match t with
  | .lbracket | .filter | .flatten => expr rbp
  | .dot => do
    let _ ← nextTok
    dotRhs rbp
  | _ => throw "--query の構文: 射影の後に続けられない記号がある"

partial def dotRhs (rbp : Nat) : PM Ast := do
  match ← peekTok with
  | .ident _ | .quoted _ | .star => expr rbp
  | .lbracket => do
    let _ ← nextTok
    multiList
  | .lbrace => do
    let _ ← nextTok
    multiHash
  | _ => throw "--query の構文: '.' の後に識別子がない"

partial def multiList : PM Ast := do
  let mut xs : List Ast := []
  repeat
    xs := xs ++ [← expr 0]
    match ← nextTok with
    | .comma => continue
    | .rbracket => break
    | _ => throw "--query の構文: 複数選択の後に ',' か ']' がない"
  return .multiList xs

partial def multiHash : PM Ast := do
  let mut xs : List (String × Ast) := []
  repeat
    let key ← match ← nextTok with
      | .ident s => pure s
      | .quoted s => pure s
      | _ => throw "--query の構文: 複数選択のキーがない"
    expectTok "':'" fun | .colon => true | _ => false
    xs := xs ++ [(key, ← expr 0)]
    match ← nextTok with
    | .comma => continue
    | .rbrace => break
    | _ => throw "--query の構文: 複数選択の後に ',' か '}' がない"
  return .multiHash xs

end

/-- 式全体を読む。 -/
def parse (s : String) : Except String Ast := do
  let tokens ← tokenize s
  let (ast, st) ← (expr 0).run { tokens, pos := 0 }
  match st.tokens[st.pos]? with
  | some .eof | none => return ast
  | _ => throw "--query の構文: 式の後に余分な記号がある"

/-- JSON の値の等しさ。 -/
partial def jsonEq : Json → Json → Bool
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .num a, .num b => a == b
  | .str a, .str b => a == b
  | .arr xs, .arr ys => xs.size == ys.size && (xs.zip ys).all fun (x, y) => jsonEq x y
  | .obj xs, .obj ys =>
    xs.size == ys.size && xs.all fun (k, v) => match ys.find? (·.1 == k) with
      | some (_, w) => jsonEq v w
      | none => false
  | _, _ => false

/-- JMESPath の真偽（null・false・空文字列・空配列・空オブジェクトが偽）。 -/
def truthy : Json → Bool
  | .null => false
  | .bool b => b
  | .str s => !s.isEmpty
  | .arr xs => !xs.isEmpty
  | .obj xs => !xs.isEmpty
  | .num _ => true

def typeName : Json → String
  | .null => "null"
  | .bool _ => "boolean"
  | .num _ => "number"
  | .str _ => "string"
  | .arr _ => "array"
  | .obj _ => "object"

def compareNum (op : String) (a b : Int) : Bool :=
  match op with
  | "<" => a < b
  | "<=" => a ≤ b
  | ">" => a > b
  | _ => a ≥ b

def sortJson (xs : Array Json) : Except String (Array Json) :=
  if xs.all fun | .num _ => true | _ => false then
    .ok (xs.qsort fun a b => match a, b with | .num x, .num y => x < y | _, _ => false)
  else if xs.all fun | .str _ => true | _ => false then
    .ok (xs.qsort fun a b => match a, b with | .str x, .str y => x < y | _, _ => false)
  else .error "sort には数か文字列だけの配列を渡す"

def callFn (name : String) (args : List Json) : Except String Json :=
  match name, args with
  | "length", [.str s] => .ok (.num s.length)
  | "length", [.arr xs] => .ok (.num xs.size)
  | "length", [.obj xs] => .ok (.num xs.size)
  | "keys", [.obj xs] => .ok (.arr (xs.map (.str ·.1)))
  | "values", [.obj xs] => .ok (.arr (xs.map (·.2)))
  | "sort", [.arr xs] => (sortJson xs).map .arr
  | "reverse", [.arr xs] => .ok (.arr xs.reverse)
  | "reverse", [.str s] => .ok (.str (String.ofList s.toList.reverse))
  | "max", [.arr xs] => (sortJson xs).map fun ys => ys.back?.getD .null
  | "min", [.arr xs] => (sortJson xs).map fun ys => ys[0]?.getD .null
  | "sum", [.arr xs] =>
    if xs.all fun | .num _ => true | _ => false then
      .ok (.num (xs.foldl (fun acc x => match x with | .num n => acc + n | _ => acc) 0))
    else .error "sum には数の配列を渡す"
  | "join", [.str sep, .arr xs] =>
    if xs.all fun | .str _ => true | _ => false then
      .ok (.str (sep.intercalate (xs.toList.map fun | .str s => s | _ => "")))
    else .error "join には文字列の配列を渡す"
  | "contains", [.arr xs, v] => .ok (.bool (xs.any (jsonEq · v)))
  | "contains", [.str s, .str t] => .ok (.bool ((s.splitOn t).length > 1 || t.isEmpty))
  | "starts_with", [.str s, .str t] => .ok (.bool (s.startsWith t))
  | "ends_with", [.str s, .str t] => .ok (.bool (s.endsWith t))
  | "type", [v] => .ok (.str (typeName v))
  | "to_string", [.str s] => .ok (.str s)
  | "to_string", [v] => .ok (.str (v.pretty))
  | "not_null", vs => .ok ((vs.find? fun | .null => false | _ => true).getD .null)
  | _, _ => .error s!"関数 {name} の名前か引数の型が --query で扱えない"

def sliceArr (xs : Array Json) (start stop : Option Int) : Array Json :=
  let n : Int := xs.size
  let norm (i : Int) : Nat := (if i < 0 then max (n + i) 0 else min i n).toNat
  let a := norm (start.getD 0)
  let b := norm (stop.getD n)
  xs.extract a b

/-- 式を評価する。 -/
partial def eval (e : Ast) (j : Json) : Except String Json :=
  match e with
  | .current => .ok j
  | .field name => .ok ((j.get? name).getD .null)
  | .literal v => .ok v
  | .sub l r => do eval r (← eval l j)
  | .index i => match j with
    | .arr xs =>
      let k : Int := if i < 0 then xs.size + i else i
      .ok (if 0 ≤ k then xs[k.toNat]?.getD .null else .null)
    | _ => .ok .null
  | .slice a b => match j with
    | .arr xs => .ok (.arr (sliceArr xs a b))
    | _ => .ok .null
  | .project l r => do
    match ← eval l j with
    | .arr xs =>
      let ys ← xs.mapM (eval r)
      return .arr (ys.filter fun | .null => false | _ => true)
    | _ => return .null
  | .valueProject l r => do
    match ← eval l j with
    | .obj xs =>
      let ys ← xs.mapM fun (_, v) => eval r v
      return .arr (ys.filter fun | .null => false | _ => true)
    | _ => return .null
  | .flatten l => do
    match ← eval l j with
    | .arr xs => return .arr (xs.foldl (fun acc x => match x with
        | .arr ys => acc ++ ys
        | x => acc.push x) #[])
    | _ => return .null
  | .filterProject l c r => do
    match ← eval l j with
    | .arr xs =>
      let kept ← xs.filterM fun x => return truthy (← eval c x)
      let ys ← kept.mapM (eval r)
      return .arr (ys.filter fun | .null => false | _ => true)
    | _ => return .null
  | .pipe l r => do eval r (← eval l j)
  | .or l r => do
    let a ← eval l j
    if truthy a then return a else eval r j
  | .and l r => do
    let a ← eval l j
    if truthy a then eval r j else return a
  | .not x => do return .bool (!truthy (← eval x j))
  | .cmp op l r => do
    let a ← eval l j
    let b ← eval r j
    match op with
    | "==" => return .bool (jsonEq a b)
    | "!=" => return .bool (!jsonEq a b)
    | _ => match a, b with
      | .num x, .num y => return .bool (compareNum op x y)
      | _, _ => return .null
  | .multiList xs => match j with
    | .null => .ok .null
    | _ => do return .arr (← xs.toArray.mapM (eval · j))
  | .multiHash xs => match j with
    | .null => .ok .null
    | _ => do return .obj (← xs.toArray.mapM fun (k, x) => do return (k, ← eval x j))
  | .call name args => do callFn name (← args.mapM (eval · j))

/-- `--query` の式で JSON を絞り込む。 -/
def apply (query : String) (j : Json) : Except String Json := do
  eval (← parse query) j

end Ritsuryo.Cli.Query
