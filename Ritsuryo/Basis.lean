module

public meta import Lean
public meta import Ritsuryo.Law

/-!
# 条文の根拠と証明の ID を記録する属性

宣言に付ける 2 つの属性を定める。

- `@[ritsuryo_basis "法令名" "条項"]`: その定義や定理がどの法令のどの条項を形式化したものかを記録する。
  法令名は `Ritsuryo.laws`（`Ritsuryo.Law`）に載っているものに限り、載っていない名前はコンパイル時にエラーにする。
  1 つの宣言に複数付けてよい。
- `@[ritsuryo_proof "ID"]`: その定理が設計のどの性質（`CAL-1`、`PER-1` など）を証明したものかを記録する。

記録は Lean の環境拡張（`SimplePersistentEnvExtension`）に入り、モジュールをまたいで集まる。
`lake exe basis-report`（`Ritsuryo.Audit`、`BasisReport.lean`）がそれを読んで、条文ごとの仕様・実装・定理の対応表
`docs/basis.md` を作り、根拠のない定義や ID の抜けを検査する。

ライブラリの各モジュールはこのファイルを `meta import` で読み込む。属性はコンパイル時にだけ働くので、
CLI の実行ファイルは `Lean` 本体をリンクしない。
-/

public section

namespace Ritsuryo

open Lean

/-- `@[ritsuryo_basis]` 1 つ分の記録。宣言の名前、法令名、条項（「第140条」「第3条第2項」「本則」など）。 -/
structure BasisEntry where
  decl : Name
  law : String
  article : String
  deriving Inhabited, Repr

/-- `@[ritsuryo_basis]` の記録を貯める環境拡張。読み込んだモジュールの記録は連結して 1 つの配列にする。 -/
meta initialize basisExt : SimplePersistentEnvExtension BasisEntry (Array BasisEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

/-- 環境にある `@[ritsuryo_basis]` の記録をすべて返す。 -/
meta def basisEntries (env : Environment) : Array BasisEntry :=
  basisExt.getState env

/-- `@[ritsuryo_proof]` の記録（定理の名前と設計の ID の組）を貯める環境拡張。 -/
meta initialize proofIdExt : SimplePersistentEnvExtension (Name × String) (Array (Name × String)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

/-- 環境にある `@[ritsuryo_proof]` の記録をすべて返す。 -/
meta def proofIds (env : Environment) : Array (Name × String) :=
  proofIdExt.getState env

end Ritsuryo

/-- `ritsuryo_basis "法令名" "条項"` 属性の構文。 -/
syntax (name := ritsuryoBasis) "ritsuryo_basis " str str : attr

/-- `ritsuryo_proof "ID"` 属性の構文。 -/
syntax (name := ritsuryoProof) "ritsuryo_proof " str : attr

-- `ritsuryo_basis` の処理: 型検査の後で法令名を `Ritsuryo.laws` から探し、あれば記録する
open Lean in
meta initialize registerBuiltinAttribute {
  name := `ritsuryoBasis
  descr := "statute provision formalized by the declaration"
  applicationTime := .afterTypeChecking
  add := fun decl stx _ => do
    let `(attr| ritsuryo_basis $law:str $article:str) := stx
      | throwError "invalid ritsuryo_basis attribute"
    let lawName := law.getString
    if (Ritsuryo.Law.find? lawName).isNone then
      throwError "unknown statute '{lawName}'; add it to Ritsuryo.laws"
    modifyEnv fun env => Ritsuryo.basisExt.addEntry env
      { decl, law := lawName, article := article.getString }
}

-- `ritsuryo_proof` の処理: 定理の名前と ID の組を記録する
open Lean in
meta initialize registerBuiltinAttribute {
  name := `ritsuryoProof
  descr := "design document ID of the property proved by the theorem"
  applicationTime := .afterTypeChecking
  add := fun decl stx _ => do
    let `(attr| ritsuryo_proof $id:str) := stx
      | throwError "invalid ritsuryo_proof attribute"
    modifyEnv fun env => Ritsuryo.proofIdExt.addEntry env (decl, id.getString)
}
