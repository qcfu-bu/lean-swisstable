import Lean

/-!
# Statement-parity checker: `Std.HashMap`/`Std.HashSet` versus a drop-in replacement

`Parity.run cfg` walks every public declaration that Std has under the source namespaces of
`cfg.nsMap` and checks that the candidate library has a declaration of the same name (after
renaming the namespace) whose elaborated type is Std's type with every Std constant replaced by
its counterpart. Types are compared up to binder names (alpha-equivalence), proofs inside types
(proof irrelevance), universe-parameter names (matched by first occurrence; a different order is
a warning) and the names of `match` auxiliaries (matched by definition), but with binder infos
(explicit, implicit, strict, instance) and default values compared exactly. Binders are aligned,
so an inserted, dropped or moved hypothesis is reported as such. Attributes (`simp` in every simp set,
`grind` in every grind set, `cbv_eval`, `cbv_opaque`, `defeq`, `refl`, `symm`, `ext`,
`elab_as_elim`, eliminators, `congr`, `deprecated`, `instance` priority, reducibility,
`protected`, `noncomputable`, `class`) are compared as sets of facts. Instances are matched by
name first and by type when the names differ; a renamed instance is added to the constant map
so that statements mentioning it (`m[a]?` mentions the `GetElem?` instance) still compare.

Run it from a file that imports Std, the candidate library and this file:

```
import Std
import OAMap
import Parity
#eval Parity.run {}
```

See `parity.md` for the configuration fields and the output format.
-/

open Lean Meta Elab Command

namespace Parity

/-! ## Configuration and results -/

structure Config where
  /-- Namespace prefix renaming `Std ↦ ours`, applied to every constant (longest prefix wins). -/
  nsMap : Array (Name × Name) :=
    #[(`Std.HashMap, `OAMap.HashMap), (`Std.HashSet, `OAMap.HashSet)]
  /-- Explicit constant renamings; they take precedence over `nsMap`. -/
  constMap : Array (Name × Name) := #[]
  /-- Std declarations outside the source namespaces to check too, with their counterparts
  (e.g. `(`List.groupByKey, `OAMap.List.groupByKey)`); they are also added to the renaming. -/
  extraDecls : Array (Name × Name) := #[]
  /-- Std prefixes that are not checked (deferred or internal APIs). -/
  exclude : Array Name :=
    #[`Std.HashMap.Raw, `Std.HashSet.Raw, `Std.HashMap.Internal, `Std.HashSet.Internal]
  /-- Exact Std names that are not checked. -/
  ignore : Array Name := #[]
  /-- When nonempty, only these Std names are checked (the extras report still covers ours). -/
  only : Array Name := #[]
  checkTheorems : Bool := true
  checkDefs : Bool := true
  checkInstances : Bool := true
  /-- Also check constructors, projections, recursors and `noConfusion` of Std structures. -/
  checkStructureInternals : Bool := false
  /-- Report binder-name differences (they break named arguments `(h := _)`). -/
  checkBinderNames : Bool := true
  /-- Report universe parameters listed in another order (only `.{u}` instantiation sees it). -/
  checkUniverseOrder : Bool := true
  /-- Report public declarations of ours in the target namespaces with no Std counterpart. -/
  reportExtras : Bool := true
  /-- Report our theorems that depend on `sorryAx` or on axioms beyond the standard three. -/
  checkAxioms : Bool := true
  /-- Skip Std declarations tagged `@[deprecated]`. -/
  skipDeprecated : Bool := false
  /-- Print the translated Std statement of each missing declaration (a to-do list). -/
  showMissingStatements : Bool := false
  /-- Also list the declarations that pass. -/
  verbose : Bool := false
  /-- Maximal number of failing entries printed per section (`0` = all). -/
  maxShow : Nat := 0
  /-- Log an error (so `lean` exits with status 1) when some check fails with an error. -/
  failOnError : Bool := true
  /-- Also write the results as JSON to this file. -/
  jsonOut : Option System.FilePath := none
  deriving Inhabited

inductive Sev where
  | error | warning | info
  deriving BEq, Inhabited, Repr

def Sev.label : Sev → String
  | .error => "error" | .warning => "warning" | .info => "info"

def Sev.rank : Sev → Nat
  | .error => 2 | .warning => 1 | .info => 0

structure Issue where
  sev : Sev
  tag : String
  lines : Array String := #[]
  deriving Inhabited

structure Entry where
  kind : String
  std : Name
  ours : Name
  issues : Array Issue := #[]
  deriving Inhabited

def Entry.worst (e : Entry) : Option Sev :=
  e.issues.foldl (init := none) fun acc i =>
    match acc with
    | none => some i.sev
    | some s => if i.sev.rank > s.rank then some i.sev else some s

def Entry.isMissing (e : Entry) : Bool := e.issues.any (·.tag == "missing")

/-! ## Renaming -/

structure Ctx where
  cfg : Config
  /-- Explicit renamings, including the instances found under another name. -/
  map : NameMap Name
  /-- `nsMap` sorted by decreasing prefix length. -/
  ns : Array (Name × Name)
  /-- For a Std constant whose counterpart lists its universe parameters in another order: the
  position in ours of each of Std's universe arguments. -/
  univ : NameMap (Array Nat) := {}

def Ctx.mk' (cfg : Config) : Ctx :=
  let ns := cfg.nsMap.qsort (fun a b => a.1.getNumParts > b.1.getNumParts)
  let map := (cfg.constMap ++ cfg.extraDecls).foldl (fun m (a, b) => m.insert a b) {}
  { cfg, map, ns }

/-- Pairs `(i, j)`: Std's universe parameter `i` corresponds to ours' parameter `j`. Parameters
are matched in order of first occurrence in the types (so `universe v u` versus Std's
`universe u v` still lines up `{α : Type u} {β : Type v}`), the rest positionally. Requires the
same number of parameters. -/
def levelCorrespondence (s c : ConstantInfo) : Array Nat := Id.run do
  let n := s.levelParams.length
  let so := (collectLevelParams {} s.type).params.filterMap (s.levelParams.idxOf? ·)
  let co := (collectLevelParams {} c.type).params.filterMap (c.levelParams.idxOf? ·)
  let mut perm : Array (Option Nat) := Array.replicate n none
  let mut used : Array Bool := Array.replicate n false
  for (i, j) in so.zip co do
    if i < n && j < n && !used[j]! then
      perm := perm.set! i (some j)
      used := used.set! j true
  -- the parameters that occur in neither type: positionally among the free slots
  let free := (List.range n).filter (!used[·]!)
  let mut k := 0
  let mut out := #[]
  for i in [0:n] do
    match perm[i]! with
    | some j => out := out.push j
    | none => out := out.push (free.getD k i); k := k + 1
  return out

/-- Registers the universe permutation of `std ↦ ours` when it is not the identity. -/
def Ctx.addUniv (ctx : Ctx) (env : Environment) (std ours : Name) : Ctx := Id.run do
  let (some s, some c) := (env.find? std, env.find? ours) | return ctx
  if s.levelParams.length != c.levelParams.length || s.levelParams.isEmpty then return ctx
  let perm := levelCorrespondence s c
  if perm == (Array.range perm.size) then return ctx
  return { ctx with univ := ctx.univ.insert std perm }

def Ctx.tr (ctx : Ctx) (n : Name) : Name :=
  match ctx.map.find? n with
  | some n' => n'
  | none =>
    match ctx.ns.find? (fun (s, _) => s.isPrefixOf n) with
    | some (s, d) => n.replacePrefix s d
    | none => n

/-- Inverse renaming, used to find our declarations without a Std counterpart. -/
def Ctx.untr (ctx : Ctx) (n : Name) : Name := Id.run do
  for (a, b) in ctx.map.toList do
    if b == n then return a
  let ns := ctx.ns.qsort (fun a b => a.2.getNumParts > b.2.getNumParts)
  match ns.find? (fun (_, d) => d.isPrefixOf n) with
  | some (s, d) => n.replacePrefix d s
  | none => n

def permuteLevels (perm : Array Nat) (us : List Level) : List Level := Id.run do
  let mut out : Array Level := Array.replicate us.length Level.zero
  for (u, j) in us.zip perm.toList do
    if j < out.size then out := out.set! j u
  return out.toList

partial def Ctx.trExpr (ctx : Ctx) (e : Expr) : Expr :=
  e.replace fun
    | .const n us =>
      let us := match ctx.univ.find? n with
        | some perm => if perm.size == us.length then permuteLevels perm us else us
        | none => us
      some (.const (ctx.tr n) us)
    | .proj s i b => some (.proj (ctx.tr s) i (ctx.trExpr b))
    | _ => none

def isUnder (pres : Array Name) (n : Name) : Bool := pres.any (·.isPrefixOf n)

/-! ## Normalisation and structural comparison -/

/-- Marker that replaces erased proofs. -/
def proofMarker : Name := `Parity.«erased proof»

/-- Replaces every application of a theorem by a marker: proofs inside statements are irrelevant
(two proofs of the same proposition are definitionally equal), and the auxiliary `_proof_i`
lemmas that Lean abstracts out of a statement have library-specific names. -/
def eraseProofs (env : Environment) (e : Expr) : Expr :=
  e.replace fun t =>
    match t.getAppFn with
    | .const c _ => if env.find? c matches some (.thmInfo _) then some (mkConst proofMarker) else none
    | _ => none

/-- Structural equality ignoring binder names and metadata, comparing binder infos (unless
`ignoreBI`), with levels compared up to normalisation. -/
partial def eqT (a b : Expr) (ignoreBI := false) : Bool :=
  let eq (x y : Expr) := eqT x y ignoreBI
  let bi (i j : BinderInfo) := ignoreBI || i == j
  match a.consumeMData, b.consumeMData with
  | .bvar i, .bvar j => i == j
  | .fvar x, .fvar y => x == y
  | .mvar x, .mvar y => x == y
  | .sort u, .sort v => u.isEquiv v
  | .const m us, .const n vs =>
    m == n && us.length == vs.length && (us.zip vs).all fun (u, v) => u.isEquiv v
  | .app f x, .app g y => eq f g && eq x y
  | .lam _ d b i, .lam _ d' b' i' => bi i i' && eq d d' && eq b b'
  | .forallE _ d b i, .forallE _ d' b' i' => bi i i' && eq d d' && eq b b'
  | .letE _ t v b _, .letE _ t' v' b' _ => eq t t' && eq v v' && eq b b'
  | .lit l, .lit l' => l == l'
  | .proj s i x, .proj s' i' y => s == s' && i == i' && eq x y
  | _, _ => false

/-- Which of the first `n` arguments of `f` are explicit (all, when `f` is not a constant). -/
def explicitMask (f : Expr) (n : Nat) : MetaM (Array Bool) := do
  let some c := f.constName? | return Array.replicate n true
  let some ci := (← getEnv).find? c | return Array.replicate n true
  let (bs, _) := peelBinders ci.type
  return (Array.range n).map fun i => if h : i < bs.size then bs[i] == .default else true
where
  peelBinders : Expr → Array BinderInfo × Unit
    | e => go e #[]
  go : Expr → Array BinderInfo → Array BinderInfo × Unit
    | .forallE _ _ b bi, acc => go b (acc.push bi)
    | .mdata _ e, acc => go e acc
    | _, acc => (acc, ())

/-- A small pair of differing subterms: descends while exactly one component differs, or
exactly one explicit argument (implicit and instance arguments often differ only because an
explicit one does). -/
partial def firstDiff (lctx : LocalContext) (a b : Expr) :
    MetaM (LocalContext × Expr × Expr) := do
  let a := a.consumeMData
  let b := b.consumeMData
  match a, b with
  | .app .., .app .. =>
    let as := a.getAppArgs
    let bs := b.getAppArgs
    if as.size == bs.size && eqT a.getAppFn b.getAppFn then
      let diffs := (List.range as.size).filter fun i => !eqT as[i]! bs[i]!
      match diffs with
      | [i] => firstDiff lctx as[i]! bs[i]!
      | _ =>
        let mask ← explicitMask a.getAppFn as.size
        match diffs.filter (mask[·]!) with
        | [i] => firstDiff lctx as[i]! bs[i]!
        | _ => return (lctx, a, b)
    else return (lctx, a, b)
  | .forallE n d body bi, .forallE _ d' body' bi'
  | .lam n d body bi, .lam _ d' body' bi' =>
    if bi != bi' then return (lctx, a, b)
    if !eqT d d' then
      return (← if eqT body body' then firstDiff lctx d d' else pure (lctx, a, b))
    let fid ← mkFreshFVarId
    let lctx := lctx.mkLocalDecl fid n d bi
    firstDiff lctx (body.instantiate1 (.fvar fid)) (body'.instantiate1 (.fvar fid))
  | _, _ => return (lctx, a, b)

/-! ## Pretty printing -/

def ppIn (lctx : LocalContext) (e : Expr) (explicit := false) (all := false) : MetaM String :=
  withLCtx lctx #[] do
    let opts (o : Options) :=
      if all then o.setBool `pp.all true
      else if explicit then (o.setBool `pp.explicit true).setBool `pp.universes true
      else o
    withOptions opts do
      let f ← ppExpr e
      return f.pretty 1000000

/-- Prints two terms so that the printed strings differ, if the printer can show a difference. -/
def ppPair (lctx : LocalContext) (a b : Expr) : MetaM (String × String) := do
  let sa ← ppIn lctx a
  let sb ← ppIn lctx b
  if sa != sb then return (sa, sb)
  let sa ← ppIn lctx a (explicit := true)
  let sb ← ppIn lctx b (explicit := true)
  if sa != sb then return (sa, sb)
  return (← ppIn lctx a (all := true), ← ppIn lctx b (all := true))

def diffLines (lctx : LocalContext) (a b : Expr) : MetaM (Array String) := do
  let (sa, sb) ← ppPair lctx a b
  let mut out := #[s!"Std : {sa}", s!"ours: {sb}"]
  let (lctx', da, db) ← firstDiff lctx a b
  unless da.equal a.consumeMData && db.equal b.consumeMData do
    let (pa, pb) ← ppPair lctx' da db
    out := out ++ #[s!"first difference:", s!"  Std : {pa}", s!"  ours: {pb}"]
  return out

def biBrackets : BinderInfo → String × String
  | .default => ("(", ")")
  | .implicit => ("{", "}")
  | .strictImplicit => ("⦃", "⦄")
  | .instImplicit => ("[", "]")

def ppName (n : Name) : String :=
  if n.hasMacroScopes then s!"{n.eraseMacroScopes}✝" else toString n

def ppBinder (lctx : LocalContext) (n : Name) (bi : BinderInfo) (ty : Expr) : MetaM String := do
  let (o, c) := biBrackets bi
  let t ← ppIn lctx ty
  if bi == .instImplicit && n.hasMacroScopes then return s!"[{t}]"
  return s!"{o}{ppName n} : {t}{c}"

def biLabel : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strict implicit"
  | .instImplicit => "instance implicit"

/-! ## Signature comparison with binder alignment -/

structure Bnd where
  name : Name
  bi : BinderInfo
  type : Expr
  deriving Inhabited

partial def peel (e : Expr) (acc : Array Bnd := #[]) : Array Bnd × Expr :=
  match e with
  | .forallE n d b bi => peel b (acc.push ⟨n, bi, d⟩)
  | .mdata _ e => peel e acc
  | e => (acc, e)

structure SigResult where
  issues : Array Issue := #[]
  /-- The binders were paired one to one (no extra or missing binder). -/
  aligned : Bool := true
  /-- No structural difference at all. -/
  equal : Bool := true

/-- Compares `std` (already translated) with `ours`. Binders are aligned greedily with a bounded
lookahead, so an inserted binder is reported as an extra hypothesis rather than as a cascade of
differences, and a dropped one as a missing hypothesis. -/
def compareSig (std ours : Expr) (checkNames : Bool) : MetaM SigResult := do
  let (sb, sBody) := peel std
  let (cb, cBody) := peel ours
  let look := 4
  let mut lctx : LocalContext := {}
  let mut sFV : Array Expr := #[]
  let mut sTy : Array Expr := #[]
  for b in sb do
    let t := b.type.instantiateRev sFV
    let id ← mkFreshFVarId
    lctx := lctx.mkLocalDecl id b.name t b.bi
    sFV := sFV.push (.fvar id)
    sTy := sTy.push t
  let mut cFV : Array Expr := #[]
  let mut i := 0
  let mut j := 0
  let mut issues : Array Issue := #[]
  -- binders of ours not (yet) matched: (index, name, info, type)
  let mut extras : Array (Nat × Name × BinderInfo × Expr) := #[]
  -- binders of Std not (yet) matched
  let mut missing : Array Nat := #[]
  -- matched binders at different positions: (Std index, our index)
  let mut moved : Array (Nat × Nat) := #[]
  let mut aligned := true
  while i < sb.size || j < cb.size do
    let ct? := if j < cb.size then some (cb[j]!.type.instantiateRev cFV) else none
    if i < sb.size then
      if let some ct := ct? then
        if eqT sTy[i]! ct then
          if sb[i]!.bi != cb[j]!.bi then
            issues := issues.push { sev := .error, tag := "binder-info", lines :=
              #[s!"binder #{i + 1} {← ppBinder lctx sb[i]!.name sb[i]!.bi sTy[i]!}: Std has it \
                {biLabel sb[i]!.bi}, ours {biLabel cb[j]!.bi} \
                ({← ppBinder lctx cb[j]!.name cb[j]!.bi ct})"] }
          if checkNames && !sb[i]!.name.hasMacroScopes && sb[i]!.name != cb[j]!.name then
            issues := issues.push { sev := .warning, tag := "binder-name", lines :=
              #[s!"binder #{i + 1} is named `{ppName sb[i]!.name}` in Std, `{ppName cb[j]!.name}` \
                in ours (breaks named arguments `({ppName sb[i]!.name} := _)`)"] }
          cFV := cFV.push sFV[i]!
          i := i + 1
          j := j + 1
          continue
    -- a Std binder that matches an earlier unmatched binder of ours: it moved; link them so that
    -- the binders of ours that come later are compared against Std's
    if i < sb.size then
      if let some k := extras.findIdx? (fun (_, _, _, t) => eqT sTy[i]! t) then
        let (jj, _, _, _) := extras[k]!
        cFV := cFV.set! jj sFV[i]!
        moved := moved.push (i, jj)
        extras := extras.eraseIdx! k
        aligned := false
        i := i + 1
        continue
    -- a binder of ours that matches an earlier unmatched Std binder
    if let some ct := ct? then
      if let some k := missing.findIdx? (fun ii => eqT sTy[ii]! ct) then
        let ii := missing[k]!
        cFV := cFV.push sFV[ii]!
        moved := moved.push (ii, j)
        missing := missing.eraseIdx! k
        aligned := false
        j := j + 1
        continue
    match ct? with
    | some ct =>
      if i < sb.size then
        -- lookahead: is our binder `j` an extra one, or Std's binder `i` a missing one?
        let mut kExtra : Option Nat := none
        for k in [1:look + 1] do
          if kExtra.isNone && j + k < cb.size then
            let mut tmp := cFV
            for _ in [0:k] do
              tmp := tmp.push (.fvar (← mkFreshFVarId))
            if eqT sTy[i]! (cb[j + k]!.type.instantiateRev tmp) then kExtra := some k
        let mut kMiss : Option Nat := none
        for k in [1:look + 1] do
          if kMiss.isNone && i + k < sb.size && eqT sTy[i + k]! ct then kMiss := some k
        let choice : Option (Bool × Nat) :=
          match kExtra, kMiss with
          | some a, some b => if a ≤ b then some (true, a) else some (false, b)
          | some a, none => some (true, a)
          | none, some b => some (false, b)
          | none, none => none
        match choice with
        | some (true, _) =>
          let id ← mkFreshFVarId
          lctx := lctx.mkLocalDecl id cb[j]!.name ct cb[j]!.bi
          extras := extras.push (j, cb[j]!.name, cb[j]!.bi, ct)
          cFV := cFV.push (.fvar id)
          aligned := false
          j := j + 1
        | some (false, _) =>
          missing := missing.push i
          aligned := false
          i := i + 1
        | none =>
          let ls ← diffLines lctx sTy[i]! ct
          -- a changed default value (`optParam`/`autoParam`) is never a mere defeq difference
          let isDefault := sTy[i]!.isOptParam || ct.isOptParam || sTy[i]!.isAutoParam ||
            ct.isAutoParam
          let tag := if isDefault then "binder-default" else "binder-type"
          issues := issues.push { sev := .error, tag, lines :=
            #[s!"binder #{i + 1} differs: Std {← ppBinder lctx sb[i]!.name sb[i]!.bi sTy[i]!}, \
              ours {← ppBinder lctx cb[j]!.name cb[j]!.bi ct}"] ++ ls.map ("  " ++ ·) }
          cFV := cFV.push sFV[i]!
          i := i + 1
          j := j + 1
      else
        let id ← mkFreshFVarId
        lctx := lctx.mkLocalDecl id cb[j]!.name ct cb[j]!.bi
        extras := extras.push (j, cb[j]!.name, cb[j]!.bi, ct)
        cFV := cFV.push (.fvar id)
        aligned := false
        j := j + 1
    | none =>
      missing := missing.push i
      aligned := false
      i := i + 1
  for (ii, jj) in moved do
    issues := issues.push { sev := .error, tag := "binder-order", lines :=
      #[s!"binder {← ppBinder lctx sb[ii]!.name sb[ii]!.bi sTy[ii]!} is #{ii + 1} in Std but \
        #{jj + 1} in ours"] }
  for (jj, n, bi, t) in extras do
    issues := issues.push { sev := .error, tag := "extra-hypothesis", lines :=
      #[s!"ours has an extra binder #{jj + 1}: {← ppBinder lctx n bi t}"] }
  for ii in missing do
    let b := sb[ii]!
    let sev := if b.bi == .default then Sev.error else Sev.warning
    issues := issues.push { sev, tag := "missing-hypothesis", lines :=
      #[s!"ours lacks Std's binder #{ii + 1}: {← ppBinder lctx b.name b.bi sTy[ii]!}"] }
  let sB := sBody.instantiateRev sFV
  let cB := cBody.instantiateRev cFV
  if !eqT sB cB then
    let ls ← diffLines lctx sB cB
    issues := issues.push { sev := .error, tag := "conclusion", lines := ls }
  let equal := issues.all (fun i => i.tag == "binder-name") && aligned
  return { issues, aligned, equal }

/-! ## Attribute facts -/

def grindKind : Grind.EMatchTheoremKind → String
  | .eqLhs g => "=" ++ (if g then " gen" else "")
  | .eqRhs g => "=_" ++ (if g then " gen" else "")
  | .eqBoth g => "_=_" ++ (if g then " gen" else "")
  | .eqBwd => "←="
  | .fwd => "→"
  | .bwd g => "←" ++ (if g then " gen" else "")
  | .leftRight => "=>"
  | .rightLeft => "<="
  | .default g => "." ++ (if g then " gen" else "")
  | .user => "usr"

structure AttrDB where
  simp : NameMap (Array String) := {}
  simpKeys : NameMap (Array (Name × Array DiscrTree.Key)) := {}
  cbv : NameMap (Array String) := {}
  refl : NameSet := {}
  symm : NameSet := {}
  ext : NameMap Nat := {}
  elim : NameMap (Array String) := {}
  congr : NameSet := {}
  deriving Inhabited

def pushFact (m : NameMap (Array String)) (n : Name) (f : String) : NameMap (Array String) :=
  let a := m.getD n #[]
  if a.contains f then m else m.insert n (a.push f)

def buildAttrDB : MetaM AttrDB := do
  let env ← getEnv
  let mut db : AttrDB := {}
  -- simp sets (the default `simp` set, `seval`, ..., and grind's normaliser)
  let mut sets : Array (Name × SimpTheorems) := #[]
  for (attr, ext) in (← simpExtensionMapRef.get).toList do
    sets := sets.push (attr, ← ext.getTheorems)
  sets := sets.push (`grind_norm, ← Grind.normExt.getTheorems)
  for (attr, st) in sets do
    let attrStr := if attr == `grind_norm then "grind norm" else toString attr
    let visit (db : AttrDB) (thm : SimpTheorem) : AttrDB := Id.run do
      let .decl n post inv := thm.origin | return db
      if st.erased.contains thm.origin then return db
      let fact := s!"@[{attrStr}{if post then "" else " ↓"}{if inv then " ←" else ""}\
        {if thm.priority != 1000 then s!" (prio {thm.priority})" else ""}]"
      let mut db := { db with simp := pushFact db.simp n fact }
      db := { db with simpKeys := db.simpKeys.insert n ((db.simpKeys.getD n #[]).push (attr, thm.keys)) }
      return db
    db := st.post.foldValues visit db
    db := st.pre.foldValues visit db
    db := st.toUnfold.fold (fun db n => { db with simp := pushFact db.simp n s!"@[{attrStr}] (unfold)" }) db
  -- cbv_eval
  let cs := Tactic.Cbv.cbvEvalExt.getState env
  for (_, es) in cs.entries.toList do
    for e in es do
      let inv := e.thm.declName != some e.origin
      db := { db with cbv := pushFact db.cbv e.origin (if inv then "@[cbv_eval ←]" else "@[cbv_eval]") }
  -- refl, symm, ext, eliminators, congr
  db := { db with refl := (Rfl.reflExt.getState env).foldValues (fun s n => s.insert n) {} }
  db := { db with symm := (Symm.symmExt.getState env).foldValues (fun s n => s.insert n) {} }
  let extMap : NameMap Nat := (Ext.extExtension.getState env).tree.foldValues
    (fun m (t : Ext.ExtTheorem) => m.insert t.declName t.priority) {}
  db := { db with ext := extMap }
  for ((ind, _), n) in (customEliminatorExt.getState env).map.toList do
    let f := if ind then "@[induction_eliminator]" else "@[cases_eliminator]"
    db := { db with elim := pushFact db.elim n f }
  for (_, thms) in (congrExtension.getState env).lemmas.toList do
    for t in thms do
      db := { db with congr := db.congr.insert t.theoremName }
  return db

/-- The attribute-like facts of a declaration, with names inside translated by `tr`. -/
def facts (db : AttrDB) (tr : Name → Name) (n : Name) : MetaM (Array String) := do
  let env ← getEnv
  let mut fs : Array String := db.simp.getD n #[]
  -- grind sets
  for (attr, ext) in (← Grind.extensionMapRef.get).toList do
    let s := ext.getState env
    if s.ematch.contains (.decl n) then
      for thm in s.ematch.find (.decl n) do
        let f := s!"@[{attr}{if thm.minIndexable then "!" else ""} {grindKind thm.kind}]"
        unless fs.contains f do fs := fs.push f
    if s.extThms.contains n then fs := fs.push s!"@[{attr} ext]"
    if let some eager := s.casesTypes.casesMap.find? n then
      fs := fs.push s!"@[{attr} cases{if eager then " eager" else ""}]"
    if s.inj.contains (.decl n) then fs := fs.push s!"@[{attr} inj]"
    if s.funCC.contains n then fs := fs.push s!"@[{attr} funCC]"
  fs := fs ++ db.cbv.getD n #[]
  if (Tactic.Cbv.cbvOpaqueExt.getState env).contains n then fs := fs.push "@[cbv_opaque]"
  if defeqAttr.hasTag env n then fs := fs.push "@[defeq]"
  if db.refl.contains n then fs := fs.push "@[refl]"
  if db.symm.contains n then fs := fs.push "@[symm]"
  if let some p := db.ext.find? n then
    fs := fs.push s!"@[ext{if p != 1000 then s!" (prio {p})" else ""}]"
  if Elab.Term.elabAsElim.hasTag env n then fs := fs.push "@[elab_as_elim]"
  fs := fs ++ db.elim.getD n #[]
  if db.congr.contains n then fs := fs.push "@[congr]"
  if let some d := Linter.deprecatedAttr.getParam? env n then
    fs := fs.push s!"@[deprecated{match d.newName? with | some m => s!" {tr m}" | none => ""}]"
  if let some ie := (instanceExtension.getState env).instanceNames.find? n then
    let kind := match ie.attrKind with
      | .global => "" | .local => "local " | .scoped => "scoped "
    fs := fs.push s!"@[{kind}instance{if ie.priority != 1000 then s!" {ie.priority}" else ""}]"
  match env.find? n with
  | some (.defnInfo _) | some (.opaqueInfo _) =>
    let r := getReducibilityStatusCore env n
    unless r == .semireducible do fs := fs.push s!"@{r.toAttrString}"
    if isNoncomputable env n then fs := fs.push "noncomputable"
  | some (.inductInfo _) =>
    if isClass env n then fs := fs.push "class"
  | _ => pure ()
  if isProtected env n then fs := fs.push "protected"
  return fs

/-- Severity of an attribute fact that Std has and ours lacks (`missing := true`) or the reverse. -/
def factSev (f : String) (missing : Bool) : Sev :=
  if f.startsWith "@[defeq]" then (if missing then .error else .info)
  else if f.startsWith "@[deprecated" then .warning
  else if f.startsWith "@[" && (f.splitOn "reducible").length > 1 then .warning
  else if f == "noncomputable" then (if missing then .info else .error)
  else .error

/-! ## Declaration classification -/

def internalSuffixes : List String :=
  ["rec", "recOn", "casesOn", "noConfusion", "noConfusionType", "ctorIdx", "ctorElim",
   "ctorElimType", "below", "brecOn", "binductionOn", "ibelow"]

/-- Constructors, projections, recursors and the other auxiliary declarations of an inductive. -/
def isStructureInternal (env : Environment) (n : Name) : Bool := Id.run do
  match env.find? n with
  | some (.ctorInfo _) | some (.recInfo _) => return true
  | _ => pure ()
  if env.isProjectionFn n || isAuxRecursor env n || isNoConfusion env n then return true
  match n with
  | .str p s =>
    match env.find? p with
    | some (.ctorInfo _) => return true
    | some (.inductInfo _) => return internalSuffixes.contains s
    | _ => return false
  | _ => return false

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor" | .quotInfo _ => "quot"

/-- Constants of a translated statement that do not exist (no counterpart in ours). -/
def unknownConsts (env : Environment) (e : Expr) : Array Name :=
  (e.getUsedConstants.filter fun c => c != proofMarker && !env.contains c).toList.eraseDups.toArray

/-! ## Checking one declaration -/

/-- Renames ours' universe parameters to Std's (see `levelCorrespondence`). -/
def levelSubst (std ours : ConstantInfo) : List Name × List Level :=
  let sl := std.levelParams
  let cl := ours.levelParams
  if sl.length == cl.length then
    let perm := levelCorrespondence std ours
    ((List.range sl.length).map (fun i => cl[perm[i]!]!), sl.map mkLevelParam)
  else
    let k := min sl.length cl.length
    (cl.take k, (sl.take k).map mkLevelParam)

def renameLevels (std ours : ConstantInfo) : Expr × Array Issue :=
  let sl := std.levelParams
  let cl := ours.levelParams
  let (ns, ls) := levelSubst std ours
  let t := ours.type.instantiateLevelParams ns ls
  if sl.length != cl.length then
    (t, #[{ sev := .error, tag := "universe", lines :=
      #[s!"Std has universe parameters {sl}, ours {cl}"] }])
  else if levelCorrespondence std ours != Array.range sl.length then
    (t, #[{ sev := .warning, tag := "universe", lines :=
      #[s!"universe parameters in another order: Std {sl}, ours {cl} (matters only for \
        explicit `.\{u}` instantiation)"] }])
  else (t, #[])

/-- Compares the signatures, universes, attributes and (for theorems) axioms of `stdName` and
its counterpart `oursName`. -/
def checkPair (ctx : Ctx) (db : AttrDB) (kind : String) (stdName oursName : Name) :
    MetaM Entry := do
  let env ← getEnv
  let some sInfo := env.find? stdName | throwError "unknown {stdName}"
  let some cInfo := env.find? oursName | do
    let mut lines := #[s!"no declaration `{oursName}`"]
    if ctx.cfg.showMissingStatements then
      let t := ctx.trExpr (eraseProofs env sInfo.type)
      lines := lines.push s!"expected type: {← ppIn {} t}"
    return { kind, std := stdName, ours := oursName,
             issues := #[{ sev := .error, tag := "missing", lines }] }
  let mut issues : Array Issue := #[]
  if kindOf sInfo != kindOf cInfo then
    issues := issues.push { sev := .info, tag := "kind", lines :=
      #[s!"Std's is a {kindOf sInfo}, ours a {kindOf cInfo}"] }
  let (cTy, uIss) := renameLevels sInfo cInfo
  issues := issues ++ uIss.filter (fun i => ctx.cfg.checkUniverseOrder || i.sev != .warning)
  let sT := ctx.trExpr (eraseProofs env sInfo.type)
  let cT := eraseProofs env cTy
  let r ← compareSig sT cT ctx.cfg.checkBinderNames
  issues := issues ++ r.issues
  if !r.equal then
    let unk := unknownConsts env sT
    unless unk.isEmpty do
      issues := issues.push { sev := .info, tag := "unmapped", lines :=
        #[s!"the translated Std statement mentions constants that ours lacks: {unk.toList}"] }
    -- downgrade to a warning when the statements are definitionally equal at instance transparency
    if r.aligned && !(sT.getUsedConstants.contains proofMarker) && unk.isEmpty then
      let sOrig := ctx.trExpr sInfo.type
      let ok ← try withTransparency .instances <| withNewMCtxDepth <| isDefEq sOrig cTy
        catch _ => pure false
      let soft (i : Issue) := i.sev == .error && (i.tag == "conclusion" || i.tag == "binder-type")
      if ok && issues.any soft then
        issues := issues.map fun i => if soft i then { i with sev := .warning } else i
        issues := issues.push { sev := .warning, tag := "defeq-only", lines :=
          #[s!"the statements differ syntactically but are defeq at instances transparency \
            (`rw`/`simp` may still behave differently)"] }
  -- notations: compare the parser descriptions
  if sInfo.type.isConstOf ``ParserDescr || sInfo.type.isConstOf ``TrailingParserDescr then
    if let (some sv, some cv) := (sInfo.value?, cInfo.value?) then
      unless eqT (ctx.trExpr sv) cv do
        issues := issues.push { sev := .error, tag := "notation", lines :=
          #[s!"Std : {← ppIn {} sv}", s!"ours: {← ppIn {} cv}"] }
  -- attributes
  let sf ← facts db ctx.tr stdName
  let cf ← facts db id oursName
  let miss := sf.filter (!cf.contains ·)
  let extra := cf.filter (!sf.contains ·)
  for f in miss do
    issues := issues.push { sev := factSev f true, tag := "attribute", lines :=
      #[s!"Std has {f}, ours does not"] }
  for f in extra do
    issues := issues.push { sev := factSev f false, tag := "attribute", lines :=
      #[s!"ours has {f}, Std does not"] }
  -- simp discrimination keys (they differ when our definitions have other reducibility)
  if r.equal then
    let sk := db.simpKeys.getD stdName #[]
    let ck := db.simpKeys.getD oursName #[]
    for (set, keys) in sk do
      if let some (_, keys') := ck.find? (·.1 == set) then
        let keysT := keys.map fun
          | .const n a => .const (ctx.tr n) a
          | .proj s i a => .proj (ctx.tr s) i a
          | k => k
        unless keysT == keys' do
          issues := issues.push { sev := .error, tag := "simp-keys", lines :=
            #[s!"@[{set}] discrimination keys differ: Std {keysT.toList.map fun k => (format k).pretty}, ours {keys'.toList.map fun k => (format k).pretty}"] }
  -- grind patterns of entries of the same kind, when the binders line up (patterns index them)
  if r.equal && r.aligned then
    let (ns, ls) := levelSubst sInfo cInfo
    for (attr, ext) in (← Grind.extensionMapRef.get).toList do
      let s := ext.getState env
      let cThms := s.ematch.find (.decl oursName)
      for t in s.ematch.find (.decl stdName) do
        let some t' := cThms.find? (fun t' => t'.kind == t.kind && t'.minIndexable == t.minIndexable)
          | continue
        let sp := t.patterns.map fun p => eraseProofs env (ctx.trExpr p)
        let cp := t'.patterns.map fun p => eraseProofs env (p.instantiateLevelParams ns ls)
        unless sp.length == cp.length && (sp.zip cp).all (fun (x, y) => eqT x y) do
          issues := issues.push { sev := .error, tag := "grind-patterns", lines :=
            #[s!"@[{attr} {grindKind t.kind}] patterns differ: Std {sp}, ours {cp}"] }
  -- axioms of our theorems
  if ctx.cfg.checkAxioms && cInfo matches .thmInfo _ then
    let axs ← collectAxioms oursName
    let bad := axs.filter fun a => ![``propext, ``Classical.choice, ``Quot.sound].contains a
    unless bad.isEmpty do
      let sev := if bad.contains ``sorryAx then Sev.error else Sev.warning
      issues := issues.push { sev, tag := "axioms", lines := #[s!"ours depends on {bad.toList}"] }
  return { kind, std := stdName, ours := oursName, issues }

/-! ## Instances: match by name, else by type -/

def matchInstances (ctx : Ctx) (db : AttrDB) (stdInsts : Array Name) : MetaM (Ctx × Array Entry) := do
  let env ← getEnv
  let targets := ctx.ns.map (·.2)
  -- our instances: those whose type mentions a constant of the target namespaces
  let pool := (instanceExtension.getState env).instanceNames.toList.filterMap fun (n, _) =>
    match env.find? n with
    | some ci => if ci.type.getUsedConstants.any (isUnder targets) then some (n, ci) else none
    | none => none
  let mut ctx := ctx
  let mut out := #[]
  for sn in stdInsts do
    let some sInfo := env.find? sn | continue
    let on := ctx.tr sn
    if (env.find? on).isSome && isInstanceCore env on then
      out := out.push (← checkPair ctx db "instance" sn on)
      continue
    let sT := ctx.trExpr (eraseProofs env sInfo.type)
    -- an instance of ours with exactly the translated type
    let exact := pool.find? fun (_, ci) =>
      let (t, u) := renameLevels sInfo ci
      u.isEmpty && eqT sT (eraseProofs env t)
    match exact with
    | some (cn, _) =>
      ctx := Ctx.addUniv { ctx with map := ctx.map.insert sn cn } env sn cn
      let e ← checkPair ctx db "instance" sn cn
      let note : Issue := ⟨.warning, "renamed",
        #[s!"found under another name: `{cn}` (statements are translated with it)"]⟩
      out := out.push { e with issues := e.issues.push note }
    | none =>
      -- same class and same conclusion, other binders: report the differences
      let (_, sBody) := peel sInfo.type
      let cls := sBody.getAppFn.constName?
      let mut best : Option (Name × Entry) := none
      for (cn, ci) in pool do
        let (_, cBody) := peel ci.type
        if cBody.getAppFn.constName? != cls then continue
        let (t, _) := renameLevels sInfo ci
        let r ← compareSig sT (eraseProofs env t) false
        if r.issues.any (·.tag == "conclusion") then continue
        let e ← checkPair ctx db "instance" sn cn
        match best with
        | some (_, b) => if e.issues.size < b.issues.size then best := some (cn, e)
        | none => best := some (cn, e)
      match best with
      | some (cn, e) =>
        ctx := Ctx.addUniv { ctx with map := ctx.map.insert sn cn } env sn cn
        let note : Issue := ⟨.warning, "renamed", #[s!"closest instance of ours: `{cn}`"]⟩
        out := out.push { e with issues := e.issues.push note }
      | none =>
        let mut lines := #[s!"no instance of type {← ppIn {} sT}"]
        if (env.find? on).isSome then lines := lines.push s!"(`{on}` exists but is not an instance)"
        out := out.push { kind := "instance", std := sn, ours := on,
                          issues := #[{ sev := .error, tag := "missing", lines }] }
  return (ctx, out)

/-! ## Matchers: match by definition -/

/-- The `match` auxiliaries (`foo.match_1`) used in Std's statements are mapped to ours by their
definition, not by name: Lean numbers them per declaration and shares identical ones between
declarations, so the names say nothing. -/
def matchMatchers (ctx : Ctx) (stdDecls : Array Name) : MetaM Ctx := do
  let env ← getEnv
  let targets := ctx.ns.map (·.2)
  let pool := env.constants.toList.filter fun (n, _) => isUnder targets n && isMatcherCore env n
  let same (s c : ConstantInfo) : Bool :=
    s.levelParams.length == c.levelParams.length &&
    let (ns, ls) := levelSubst s c
    let tr (e : Expr) := ctx.trExpr (eraseProofs env e)
    -- binder infos of the captured variables follow the enclosing declaration: irrelevant
    eqT (tr s.type) (eraseProofs env (c.type.instantiateLevelParams ns ls)) (ignoreBI := true) &&
    match s.value?, c.value? with
    | some sv, some cv =>
      eqT (tr sv) (eraseProofs env (cv.instantiateLevelParams ns ls)) (ignoreBI := true)
    | _, _ => false
  let mut ctx := ctx
  let mut seen : NameSet := {}
  for d in stdDecls do
    let some ci := env.find? d | continue
    for m in ci.type.getUsedConstants do
      if seen.contains m || !isMatcherCore env m then continue
      seen := seen.insert m
      let some sInfo := env.find? m | continue
      if let some cInfo := env.find? (ctx.tr m) then
        if same sInfo cInfo then continue
      if let some (cn, _) := pool.find? (fun (_, cInfo) => same sInfo cInfo) then
        ctx := Ctx.addUniv { ctx with map := ctx.map.insert m cn } env m cn
  return ctx

/-! ## Driver -/

def stdDecls (cfg : Config) (env : Environment) : Array Name := Id.run do
  let srcs := cfg.nsMap.map (·.1)
  let mut out := #[]
  for (n, _) in env.constants.toList do
    if !isUnder srcs n then continue
    if isUnder cfg.exclude n || cfg.ignore.contains n then continue
    if !cfg.only.isEmpty && !cfg.only.contains n then continue
    if isPrivateName n || n.isInternalDetail then continue
    if !cfg.checkStructureInternals && isStructureInternal env n then continue
    if cfg.skipDeprecated && Linter.isDeprecated env n then continue
    out := out.push n
  for (n, _) in cfg.extraDecls do
    if env.contains n && !out.contains n then out := out.push n
  return out.qsort Name.lt

def issueJson (i : Issue) : Json :=
  Json.mkObj [("severity", i.sev.label), ("tag", i.tag), ("lines", toJson i.lines)]

def entryJson (e : Entry) : Json :=
  let status := match e.worst with
    | none => "ok" | some .info => "ok" | some .warning => "warning" | some .error =>
      if e.isMissing then "missing" else "error"
  Json.mkObj [("kind", e.kind), ("std", toString e.std), ("ours", toString e.ours),
    ("status", status), ("issues", toJson (e.issues.map issueJson))]

def statusLabel (e : Entry) : String :=
  match e.worst with
  | none | some .info => "OK     "
  | some .warning => "WARN   "
  | some .error => if e.isMissing then "MISSING" else "ERROR  "

def renderEntry (e : Entry) : Array String := Id.run do
  let head := if e.ours == e.std then s!"{statusLabel e} {e.std}"
    else s!"{statusLabel e} {e.std}  ↦  {e.ours}"
  let mut out := #[head]
  for i in e.issues do
    match i.lines.toList with
    | [] => out := out.push s!"    [{i.sev.label}: {i.tag}]"
    | l :: ls =>
      let ind (k : Nat) (l : String) := l.replace "\n" ("\n" ++ "".pushn ' ' k)
      out := out.push s!"    [{i.sev.label}: {i.tag}] {ind 8 l}"
      for l in ls do out := out.push s!"        {ind 8 l}"
  return out

def section_ (cfg : Config) (title : String) (es : Array Entry) : Array String := Id.run do
  let bad := es.filter fun e => match e.worst with | some .error | some .warning => true | _ => false
  let mut out := #[s!"", s!"── {title}: {es.size} checked, {es.size - bad.size} ok, \
    {(bad.filter (·.isMissing)).size} missing, \
    {(bad.filter fun e => !e.isMissing && e.worst == some .error).size} with errors, \
    {(bad.filter (·.worst == some .warning)).size} with warnings only ──"]
  let shown := if cfg.verbose then es else bad
  let shown := if cfg.maxShow == 0 then shown else shown.extract 0 cfg.maxShow
  for e in shown do out := out ++ renderEntry e
  let total := if cfg.verbose then es.size else bad.size
  if shown.size < total then
    out := out.push s!"  … {total - shown.size} more (raise `maxShow`)"
  return out

/-- Runs the parity check and prints the report. -/
def run (cfg : Config := {}) : CommandElabM Unit := liftTermElabM do
  let env ← getEnv
  let mut ctx := Ctx.mk' cfg
  -- universe permutations of every renamed constant (statements mention them)
  let srcs := cfg.nsMap.map (·.1)
  for (n, _) in env.constants.toList do
    if isUnder srcs n || cfg.constMap.any (·.1 == n) || cfg.extraDecls.any (·.1 == n) then
      ctx := ctx.addUniv env n (ctx.tr n)
  let db ← buildAttrDB
  let decls := stdDecls cfg env
  let isInst (n : Name) := isInstanceCore env n
  let insts := decls.filter isInst
  let thms := decls.filter fun n => !isInst n && env.find? n matches some (.thmInfo _)
  let types := decls.filter fun n => env.find? n matches some (.inductInfo _)
  let defs := decls.filter fun n => !isInst n && !(env.find? n matches some (.thmInfo _)) &&
    !(env.find? n matches some (.inductInfo _))
  -- types first, then instances (which may extend the renaming), then the rest
  let mut tyEs := #[]
  for n in types do tyEs := tyEs.push (← checkPair ctx db "type" n (ctx.tr n))
  let mut instEs := #[]
  if cfg.checkInstances then
    let (ctx', es) ← matchInstances ctx db insts
    ctx := ctx'
    instEs := es
  ctx ← matchMatchers ctx decls
  let mut defEs := #[]
  if cfg.checkDefs then
    for n in defs do defEs := defEs.push (← checkPair ctx db "def" n (ctx.tr n))
  let mut thmEs := #[]
  if cfg.checkTheorems then
    for n in thms do thmEs := thmEs.push (← checkPair ctx db "theorem" n (ctx.tr n))
  -- root causes: a statement that mentions a Std constant whose own signature differs
  let sigTags := ["binder-info", "binder-type", "binder-default", "binder-order",
    "extra-hypothesis", "missing-hypothesis", "conclusion"]
  let isSigBad (e : Entry) := e.issues.any fun i => i.sev == .error && sigTags.contains i.tag
  let badSig : NameSet := (tyEs ++ instEs ++ defEs).foldl
    (fun s e => if isSigBad e then s.insert e.std else s) {}
  let hint (e : Entry) : Entry := Id.run do
    unless isSigBad e do return e
    let some ci := env.find? e.std | return e
    let used := ci.type.getUsedConstants.filter fun c => c != e.std && badSig.contains c
    if used.isEmpty then return e
    { e with issues := e.issues.push { sev := .info, tag := "root-cause", lines :=
        #[s!"the statement uses {used.toList.eraseDups}, whose own signatures differ \
          (see above); fix those first"] } }
  defEs := defEs.map hint
  thmEs := thmEs.map hint
  instEs := instEs.map hint
  -- extras
  let mut extras := #[]
  if cfg.reportExtras then
    let targets := cfg.nsMap.map (·.2)
    for (n, _) in env.constants.toList do
      if !isUnder targets n || isPrivateName n || n.isInternalDetail then continue
      if isStructureInternal env n then continue
      let sn := ctx.untr n
      if sn == n || !env.contains sn then extras := extras.push n
    extras := extras.qsort Name.lt
  let mut out : Array String := #[]
  let mapStr := ", ".intercalate (cfg.nsMap.toList.map fun (a, b) => s!"{a} ↦ {b}")
  out := out.push s!"Statement parity: {mapStr}"
  let renamed := ctx.map.toList.filter fun (a, _) =>
    !cfg.constMap.any (·.1 == a) && !cfg.extraDecls.any (·.1 == a) && !isMatcherCore env a
  unless renamed.isEmpty do
    out := out.push s!"instances renamed by type: {renamed.map fun (a, b) => s!"{a} ↦ {b}"}"
  out := out ++ section_ cfg "types" tyEs
  out := out ++ section_ cfg "instances" instEs
  out := out ++ section_ cfg "definitions" defEs
  out := out ++ section_ cfg "theorems" thmEs
  if cfg.reportExtras then
    out := out.push ""
    out := out.push s!"── extras (ours, no Std counterpart): {extras.size} ──"
    for n in extras do out := out.push s!"  {n}"
  let all := tyEs ++ instEs ++ defEs ++ thmEs
  let nErr := (all.filter (·.worst == some .error)).size
  let nWarn := (all.filter (·.worst == some .warning)).size
  out := out.push ""
  out := out.push s!"── summary: {all.size} Std declarations, {all.size - nErr - nWarn} ok, \
    {nErr} with errors ({(all.filter (·.isMissing)).size} missing), {nWarn} with warnings only ──"
  IO.println ("\n".intercalate out.toList)
  if let some p := cfg.jsonOut then
    let j := Json.mkObj [("entries", toJson (all.map entryJson)),
      ("extras", toJson (extras.map toString))]
    IO.FS.writeFile p j.pretty
  if cfg.failOnError && nErr > 0 then
    logError m!"parity check failed: {nErr} Std declarations with errors"

end Parity
