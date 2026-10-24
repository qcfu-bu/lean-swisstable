module

public import Std.Data.Internal.List.Associative
public import OAMap.Core.Swiss.Table

/-!
# The SwissTable core (statements; proofs to come)

The core module that `tools/select-core.sh swiss` selects: the 23 definitions of
`OAMap/Core/Swiss/Table.lean` and the 22 contract lemmas of `docs/ARCHITECTURE.md` §3.3, stated
exactly as `test/OAMapTest/CoreSpec.lean` uses them.

**Not proved yet: every lemma below is `sorry`.** Do not select this core before they are
proved; `test/OAMapTest/Audit.lean` fails on `sorryAx` once it is selected.
-/

public section

universe u v w w'

open Std.Internal.List

namespace OAMap.Core.Table

variable {α : Type u} {β : Type v} {γ : Type w} {_ : BEq α} {_ : Hashable α}

theorem distinctKeys [EquivBEq α] [LawfulHashable α] (t : Table α β) :
    DistinctKeys t.toListModel := sorry

theorem size_eq_length (t : Table α β) : t.size = t.toListModel.length := sorry

theorem toListModel_emptyWithCapacity {c : Nat} :
    (emptyWithCapacity c : Table α β).toListModel = [] := sorry

theorem lookup_emptyWithCapacity {σ : Type w} {c : Nat} {a : α} {f : α → β → σ}
    {g : Unit → σ} : (emptyWithCapacity c : Table α β).lookup a f g = g () := sorry

theorem erase_emptyWithCapacity {c : Nat} {a : α} :
    (emptyWithCapacity c : Table α β).erase a = emptyWithCapacity c := sorry

theorem contains_eq_lookup (t : Table α β) (a : α) :
    t.contains a = t.lookup a (fun _ _ => true) (fun _ => false) := sorry

theorem lookup_eq [EquivBEq α] [LawfulHashable α] {σ : Type w} (t : Table α β) (a : α)
    (f : α → β → σ) (g : Unit → σ) :
    t.lookup a f g = (getEntry? a t.toListModel).elim (g ()) (fun e => f e.1 e.2) := sorry

theorem lookupMem_eq [EquivBEq α] [LawfulHashable α] {σ : Type w} (t : Table α β) (a : α)
    (h : t.contains a = true) (f : α → β → σ) {e : (_ : α) × β}
    (he : getEntry? a t.toListModel = some e) : t.lookupMem a h f = f e.1 e.2 := sorry

theorem containsThenInsert_eq (t : Table α β) (a : α) (b : β) :
    t.containsThenInsert a b = (t.contains a, t.insert a b) := sorry

theorem containsThenInsertIfNew_eq (t : Table α β) (a : α) (b : β) :
    t.containsThenInsertIfNew a b = (t.contains a, t.insertIfNew a b) := sorry

theorem getThenInsertIfNew?_eq (t : Table α β) (a : α) (b : β) :
    t.getThenInsertIfNew? a b =
      (t.lookup a (fun _ v => some v) (fun _ => none), t.insertIfNew a b) := sorry

theorem toListModel_insert [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) (b : β) :
    (t.insert a b).toListModel.Perm (insertEntry a b t.toListModel) := sorry

theorem toListModel_insertIfNew [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α)
    (b : β) : (t.insertIfNew a b).toListModel.Perm (insertEntryIfNew a b t.toListModel) := sorry

theorem toListModel_erase [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) :
    (t.erase a).toListModel.Perm (eraseKey a t.toListModel) := sorry

theorem toListModel_alter [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α)
    (f : Option β → Option β) :
    (t.alter a f).toListModel.Perm (Const.alterKey a f t.toListModel) := sorry

theorem toListModel_modify [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α)
    (f : β → β) : (t.modify a f).toListModel.Perm (Const.modifyKey a f t.toListModel) := sorry

theorem toListModel_filter (t : Table α β) (f : α → β → Bool) :
    (t.filter f).toListModel.Perm (t.toListModel.filter fun p => f p.1 p.2) := sorry

theorem toListModel_filterMap (t : Table α β) (f : α → β → Option γ) :
    (t.filterMap f).toListModel.Perm
      (t.toListModel.filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)) := sorry

theorem toListModel_map (t : Table α β) (f : α → β → γ) :
    (t.map f).toListModel.Perm (t.toListModel.map fun p => ⟨p.1, f p.1 p.2⟩) := sorry

theorem foldM_eq_foldlM_toListModel {ε : Type w} {m : Type w → Type w'} [Monad m]
    [LawfulMonad m] (t : Table α β) (f : ε → α → β → m ε) (init : ε) :
    t.foldM f init = t.toListModel.foldlM (fun d e => f d e.1 e.2) init := sorry

theorem foldRev_eq_foldr_toListModel {ε : Type w} (t : Table α β) (f : ε → α → β → ε)
    (init : ε) : t.foldRev f init = t.toListModel.foldr (fun e d => f d e.1 e.2) init := sorry

theorem forIn_eq_forIn_toListModel {ε : Type w} {m : Type w → Type w'} [Monad m]
    [LawfulMonad m] (t : Table α β) (f : α → β → ε → m (ForInStep ε)) (init : ε) :
    t.forIn f init = ForIn.forIn t.toListModel init (fun e d => f e.1 e.2 d) := sorry

end OAMap.Core.Table
