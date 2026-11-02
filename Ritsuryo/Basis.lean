module

public meta import Lean
public meta import Ritsuryo.Law

public section

namespace Ritsuryo

open Lean

structure BasisEntry where
  decl : Name
  law : String
  article : String
  deriving Inhabited, Repr

meta initialize basisExt : SimplePersistentEnvExtension BasisEntry (Array BasisEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

meta def basisEntries (env : Environment) : Array BasisEntry :=
  basisExt.getState env

meta initialize proofIdExt : SimplePersistentEnvExtension (Name × String) (Array (Name × String)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

meta def proofIds (env : Environment) : Array (Name × String) :=
  proofIdExt.getState env

end Ritsuryo

syntax (name := ritsuryoBasis) "ritsuryo_basis " str str : attr

syntax (name := ritsuryoProof) "ritsuryo_proof " str : attr

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
