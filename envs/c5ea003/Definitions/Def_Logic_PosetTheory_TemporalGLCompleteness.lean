-- Prove2me | Definitions.Def_Logic_PosetTheory_TemporalGLCompleteness
-- name    : Logic_PosetTheory_TemporalGLCompleteness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:03:15.000313+00:00
-- url     : https://prove2.me/theorems/f332f2fd-3944-4472-b9e6-583dfcb278ab
-- title:
--   Aether Catalog definitions — Logic_PosetTheory_TemporalGLCompleteness
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.PosetTheory.TemporalGLCompleteness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/PosetTheory/TemporalGLCompleteness.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_PosetTheory_TemporalGL
import Definitions.Def_Logic_PosetTheory_TemporalGLDeduction
import Definitions.Def_Logic_PosetTheory_TemporalGLFiniteModel
import Definitions.Def_Logic_PosetTheory_TemporalGLSyntax

/-!
# Temporal Gödel–Löb logic: the finite canonical model and completeness

This file closes the last gap in the finite-model conjecture for the calculus TGL.
Rather than building an (infinite) canonical model — which for Gödel–Löb logic is *not*
a legal frame, since converse well-foundedness fails — we build the **finite canonical
model over the subformula closure of a single formula**, using exactly the relations
`filtR` / `filtT` from `TemporalGLFiniteModel.lean`.

Worlds are the consistent "decided subsets" `t ⊆ Cl` of a subformula-closed finite set
`Cl`: the list `gammaList Cl t` asserts every member of `t` and the negation of every
member of `Cl \ t`, and `t` is a world when that list is TGL-consistent.

The two existence lemmas are the mathematical core:

* `exists_box_succ` — if `◻B ∉ t`, there is a world `s` with `filtR Cl t s` and `B ∉ s`.
  Its proof runs the classical **Löb argument**: were the candidate hypothesis list
  inconsistent, boxing it and applying Löb's axiom would force `◻B ∈ t`.
* `exists_glob_succ` — the temporal analogue, whose proof uses `◼`-necessitation, the
  `4` axiom for `◼`, and the interaction axiom `◻A ⟹ ◼◻A`.

Combining these with the truth lemma `can_truth_lemma` yields

* `completeness` — every valid formula is derivable, and
* `finite_model_property` — **the conjecture**: every non-derivable `A` has a
  `TemporalGL.TempFrame` countermodel with at most `2 ^ (2 * subformulaCount A)` worlds.
-/

namespace TemporalGLDeep

open TemporalGL

/-! ## 1. Subformula-closed sets -/

/-- A finite set of formulas closed under immediate subformulas. -/
structure Closed (Cl : Finset TForm) : Prop where
  /-- Closure under the two immediate subformulas of an implication. -/
  imp : ∀ {B C : TForm}, (B ⟹ C) ∈ Cl → B ∈ Cl ∧ C ∈ Cl
  /-- Closure under un-boxing. -/
  box : ∀ {B : TForm}, (◻B) ∈ Cl → B ∈ Cl
  /-- Closure under removing a temporal box. -/
  glob : ∀ {B : TForm}, (◼B) ∈ Cl → B ∈ Cl


/-- Remove one `◻`. -/
def TForm.unbox : TForm → TForm
  | .box C => C
  | X => X

/-- Remove one `◼`. -/
def TForm.unglob : TForm → TForm
  | .glob C => C
  | X => X

/-! ## 2. Decided subsets and consistency -/

/-- The hypothesis list determined by `t ⊆ Cl`: each formula of `Cl` is asserted if it
lies in `t` and negated otherwise. -/
noncomputable def gammaList (Cl t : Finset TForm) : List TForm :=
  Cl.toList.map (fun B => if B ∈ t then B else B.neg)

theorem mem_gammaList_pos {Cl t : Finset TForm} {B : TForm} (h₁ : B ∈ Cl) (h₂ : B ∈ t) :
    B ∈ gammaList Cl t := by
  refine List.mem_map.2 ⟨B, Finset.mem_toList.2 h₁, ?_⟩
  simp [h₂]

theorem mem_gammaList_neg {Cl t : Finset TForm} {B : TForm} (h₁ : B ∈ Cl) (h₂ : B ∉ t) :
    B.neg ∈ gammaList Cl t := by
  refine List.mem_map.2 ⟨B, Finset.mem_toList.2 h₁, ?_⟩
  simp [h₂]

/-- `t` is a *consistent decided subset* of `Cl`. -/
def Cons (Cl t : Finset TForm) : Prop := ListCons (gammaList Cl t)

/-- Anything derivable from a consistent decided subset and lying in `Cl` belongs to it. -/
theorem mem_of_Der {Cl t : Finset TForm} (hc : Cons Cl t) {B : TForm} (hB : B ∈ Cl)
    (h : Der (gammaList Cl t) B) : B ∈ t := by
  by_contra hn
  exact hc (Der_mp (Der_of_mem (mem_gammaList_neg hB hn)) h)

/-- The worlds of the finite canonical model over `Cl`. -/
noncomputable def CanW (Cl : Finset TForm) : Finset (Finset TForm) :=
  @Finset.filter _ (fun t => Cons Cl t) (Classical.decPred _) Cl.powerset

theorem mem_CanW {Cl t : Finset TForm} : t ∈ CanW Cl ↔ t ⊆ Cl ∧ Cons Cl t := by
  simp only [CanW, Finset.mem_filter, Finset.mem_powerset]


/-! ## 3. Lists of boxed / temporally boxed members of a world -/

/-- The `◻`-formulas of `Cl` belonging to `t`. -/
noncomputable def boxList (Cl t : Finset TForm) : List TForm :=
  Cl.toList.filter (fun C => C.isBox && decide (C ∈ t))

/-- The `◼`-formulas of `Cl` belonging to `t`. -/
noncomputable def globList (Cl t : Finset TForm) : List TForm :=
  Cl.toList.filter (fun C => C.isGlob && decide (C ∈ t))





/-! ## 4. The two existence lemmas -/



/-! ## 5. The finite canonical model -/

/-- The worlds of the canonical model over `Cl`. -/
def CanWorld (Cl : Finset TForm) : Type := {t : Finset TForm // t ∈ CanW Cl}

noncomputable instance (Cl : Finset TForm) : Fintype (CanWorld Cl) := FinsetCoe.fintype _

/-- **The finite canonical frame.**  Accessibility and the temporal order are the
filtration relations of `TemporalGLFiniteModel.lean`; Löb's condition is the counting
argument `filtR_wf`, reflexivity of time comes from the axiom `◼A ⟹ A`, and the
interaction condition is `filtT_filtR_compat`. -/
noncomputable def canFrame (Cl : Finset TForm) (hCl : Closed Cl) : TempFrame where
  W := CanWorld Cl
  R := fun t s => filtR Cl t.1 s.1
  T := fun t s => filtT Cl t.1 s.1
  R_trans := fun _ _ _ h₁ h₂ => filtR_trans _ h₁ h₂
  R_wf := filtR_wf Cl (fun t : CanWorld Cl => t.1)
  T_refl := by
    intro t
    refine ⟨fun E hECl hEt => ⟨?_, hEt⟩, fun _ _ h => h⟩
    exact mem_of_Der (mem_CanW.1 t.2).2 (hCl.glob hECl)
      (Der_mp (Der_of_derivable Derivable.globT) (Der_of_mem (mem_gammaList_pos hECl hEt)))
  T_trans := fun _ _ _ h₁ h₂ => filtT_trans _ h₁ h₂
  compat := fun hT hR => filtT_filtR_compat _ hT hR

/-- The canonical model: an atom holds at a world iff it belongs to it. -/
noncomputable def canModel (Cl : Finset TForm) (hCl : Closed Cl) : TempModel where
  F := canFrame Cl hCl
  V := fun p t => (TForm.atom p) ∈ t.1



/-! ## 6. Completeness and the finite model property -/





/-! ## 7. Consequences and non-degeneracy

The results above are only interesting if TGL really is a non-trivial logic in which the
two modalities interact but do not collapse.  This section records that. -/





/-- A temporal GL frame whose time order is trivial (only the present) but whose
accessibility relation is not: `true` sees `false`, and nothing else. -/
def rigidTimeFrame : TempFrame where
  W := Bool
  R := fun a b => a = true ∧ b = false
  T := fun a b => a = b
  R_trans := by intro a b c hab hbc; revert a b c; decide
  R_wf := by
    have : Std.Irrefl (fun a b : Bool => b = true ∧ a = false) :=
      ⟨by intro a; revert a; decide⟩
    have : IsTrans Bool (fun a b : Bool => b = true ∧ a = false) :=
      ⟨by intro a b c; revert a b c; decide⟩
    exact Finite.wellFounded_of_trans_of_irrefl _
  T_refl := fun _ => rfl
  T_trans := by intro a b c hab hbc; exact hab.trans hbc
  compat := by intro w w' v h hR; cases h; exact hR

/-- The model on `rigidTimeFrame` in which the atom holds exactly at `true`. -/
def rigidModel : TempModel where
  F := rigidTimeFrame
  V := fun _ b => b = true



/-! ## 8. Machine-checked data points for the bound

The bound `2 ^ (2 * subformulaCount A)` is far from tight on concrete formulas; the two
theorems below record explicitly verified minimal countermodels, which are what a
bounded model search would actually return. -/



end TemporalGLDeep


