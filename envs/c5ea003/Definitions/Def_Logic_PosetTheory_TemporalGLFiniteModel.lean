-- Prove2me | Definitions.Def_Logic_PosetTheory_TemporalGLFiniteModel
-- name    : Logic_PosetTheory_TemporalGLFiniteModel
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:02:05.734925+00:00
-- url     : https://prove2.me/theorems/9a574d4d-9a05-4df7-ad77-7795456d3d64
-- title:
--   Aether Catalog definitions — Logic_PosetTheory_TemporalGLFiniteModel
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.PosetTheory.TemporalGLFiniteModel`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/PosetTheory/TemporalGLFiniteModel.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_PosetTheory_TemporalGL
import Definitions.Def_Logic_PosetTheory_TemporalGLSyntax

/-!
# Temporal Gödel–Löb logic: filtration and an explicit finite-model bound

This file proves the **small model property** for the temporal Gödel–Löb calculus TGL
of `TemporalGLSyntax.lean` over the catalog's frame class `TemporalGL.TempFrame`:

> if a formula `A` fails somewhere in *some* temporal GL model, then it already fails in
> a temporal GL model with at most `2 ^ (2 * subformulaCount A)` worlds.

The construction is a **filtration** through the subformulas of `A`, but a naive
filtration will not do: the quotient relation must simultaneously

* stay transitive (`TempFrame.R_trans`),
* stay **converse well-founded** (`TempFrame.R_wf`) — the Löb condition,
* keep the temporal order a preorder (`T_refl`, `T_trans`),
* and preserve the *interaction* condition `TempFrame.compat`
  (`T w w' → R w' v → R w v`), which is what validates the axiom `◻A ⟹ ◼◻A`.

The relation `filtR` below is the Segerberg-style GL filtration (successors must
*strictly increase* the set of realised boxes, which yields converse well-foundedness
from a counting argument), and `filtT` is its temporal companion, strengthened by a
`◻`-clause precisely so that `compat` survives filtration.  The strengthening is sound
because `compat` in the original model already forces `◻`-formulas to persist along `T`.

## Main results

* `filtR_measure_lt` — every `filtR`-step strictly increases the number of realised
  boxed subformulas; this is the combinatorial heart of converse well-foundedness.
* `filtFrame` — the filtered frame is a genuine `TemporalGL.TempFrame`.
* `truth_lemma` — the filtration lemma: on realised worlds the filtered model agrees
  with the original model on every subformula of `A`.
* `bounded_countermodel` — **main theorem**: any countermodel can be shrunk to one with
  at most `2 ^ subformulaCount A` (hence at most `2 ^ (2 * subformulaCount A)`) worlds.
* `finite_model_property_of_completeness` — the conjectured finite model property with
  the explicit bound `2 ^ (2 * subformulaCount A)`, for every non-derivable `A`, given
  weak completeness of TGL.
* `decidable_validity_reduces_to_bounded_check` — validity is equivalent to validity on
  models of size at most `2 ^ (2 * subformulaCount A)`, which is the statement that
  makes "exhaustive bounded model search" a correct decision procedure.
-/

namespace TemporalGLDeep

open TemporalGL

/-! ## 1. The filtration relations

Both relations are defined on arbitrary finite sets of formulas; `Cl` will always be
`subformulas A`. -/

/-- The filtered accessibility relation.  `filtR Cl S S'` holds when every boxed formula
of `Cl` realised at `S` is, together with its argument, realised at `S'`, **and** at
least one boxed formula of `Cl` is realised at `S'` but not at `S`.  The second clause
is what makes the filtered relation converse well-founded. -/
def filtR (Cl : Finset TForm) (S S' : Finset TForm) : Prop :=
  (∀ B, (◻B) ∈ Cl → (◻B) ∈ S → (B ∈ S' ∧ (◻B) ∈ S')) ∧
  (∃ B, (◻B) ∈ Cl ∧ (◻B) ∈ S' ∧ (◻B) ∉ S)

/-- The filtered temporal relation.  Besides the usual clause for `◼`, it demands that
boxed formulas persist; this extra clause is what makes `TempFrame.compat` survive
filtration, and it is satisfied by the original model precisely because of `compat`. -/
def filtT (Cl : Finset TForm) (S S' : Finset TForm) : Prop :=
  (∀ B, (◼B) ∈ Cl → (◼B) ∈ S → (B ∈ S' ∧ (◼B) ∈ S')) ∧
  (∀ B, (◻B) ∈ Cl → (◻B) ∈ S → (◻B) ∈ S')

theorem filtR_trans (Cl : Finset TForm) {S₁ S₂ S₃ : Finset TForm}
    (h₁ : filtR Cl S₁ S₂) (h₂ : filtR Cl S₂ S₃) : filtR Cl S₁ S₃ := by
  refine ⟨fun B hB hS => ?_, ?_⟩
  · exact h₂.1 B hB (h₁.1 B hB hS).2
  · obtain ⟨B, hBCl, hBS₂, hBS₁⟩ := h₁.2
    exact ⟨B, hBCl, (h₂.1 B hBCl hBS₂).2, hBS₁⟩

theorem filtT_trans (Cl : Finset TForm) {S₁ S₂ S₃ : Finset TForm}
    (h₁ : filtT Cl S₁ S₂) (h₂ : filtT Cl S₂ S₃) : filtT Cl S₁ S₃ :=
  ⟨fun B hB hS => h₂.1 B hB (h₁.1 B hB hS).2,
   fun B hB hS => h₂.2 B hB (h₁.2 B hB hS)⟩

/-- **The interaction condition survives filtration.**  This is the reason for the
second clause of `filtT`. -/
theorem filtT_filtR_compat (Cl : Finset TForm) {S S₁ S₂ : Finset TForm}
    (hT : filtT Cl S S₁) (hR : filtR Cl S₁ S₂) : filtR Cl S S₂ := by
  refine ⟨fun B hB hS => hR.1 B hB (hT.2 B hB hS), ?_⟩
  obtain ⟨B, hBCl, hBS₂, hBS₁⟩ := hR.2
  exact ⟨B, hBCl, hBS₂, fun hBS => hBS₁ (hT.2 B hBCl hBS)⟩

/-! ## 2. The counting measure and converse well-foundedness -/

/-- The boxed formulas occurring in `Cl`. -/
def boxCl (Cl : Finset TForm) : Finset TForm := Cl.filter (fun C => C.isBox)

/-- The number of boxed formulas of `Cl` realised at `S`. -/
def boxCount (Cl S : Finset TForm) : ℕ := ((boxCl Cl).filter (fun C => C ∈ S)).card

theorem boxCount_le (Cl S : Finset TForm) : boxCount Cl S ≤ (boxCl Cl).card :=
  Finset.card_filter_le _ _

theorem mem_boxCl {Cl : Finset TForm} {C : TForm} (h : C ∈ boxCl Cl) :
    ∃ B, C = ◻B ∧ (◻B) ∈ Cl := by
  simp only [boxCl, Finset.mem_filter] at h
  obtain ⟨hCl, hbox⟩ := h
  cases C with
  | box B => exact ⟨B, rfl, hCl⟩
  | atom p => simp [TForm.isBox] at hbox
  | bot => simp [TForm.isBox] at hbox
  | imp B C => simp [TForm.isBox] at hbox
  | glob B => simp [TForm.isBox] at hbox

/-- **The combinatorial heart of the construction**: a `filtR`-step strictly increases
the number of realised boxed subformulas.  Since that number is bounded by `|boxCl Cl|`,
the filtered relation is converse well-founded, i.e. the filtered frame validates Löb. -/
theorem filtR_measure_lt (Cl : Finset TForm) {S S' : Finset TForm} (h : filtR Cl S S') :
    boxCount Cl S < boxCount Cl S' := by
  have hsub : (boxCl Cl).filter (fun C => C ∈ S) ⊆ (boxCl Cl).filter (fun C => C ∈ S') := by
    intro C hC
    simp only [Finset.mem_filter] at hC ⊢
    obtain ⟨hCbox, hCS⟩ := hC
    obtain ⟨B, rfl, hBCl⟩ := mem_boxCl hCbox
    exact ⟨hCbox, (h.1 B hBCl hCS).2⟩
  obtain ⟨B, hBCl, hBS', hBS⟩ := h.2
  have hmemBox : (◻B) ∈ boxCl Cl := by
    simp only [boxCl, Finset.mem_filter]
    exact ⟨hBCl, by simp [TForm.isBox]⟩
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨◻B, ?_, ?_⟩)
  · simp only [Finset.mem_filter]; exact ⟨hmemBox, hBS'⟩
  · simp only [Finset.mem_filter]; tauto

/-- Converse well-foundedness of any relation pulled back from `filtR`, by the counting
measure.  This is what makes a filtered/canonical frame validate Löb. -/
theorem filtR_wf (Cl : Finset TForm) {α : Type} (f : α → Finset TForm) :
    WellFounded (fun a b : α => filtR Cl (f b) (f a)) := by
  have key : ∀ a b : α, filtR Cl (f b) (f a) →
      (boxCl Cl).card - boxCount Cl (f a) < (boxCl Cl).card - boxCount Cl (f b) := by
    intro a b h
    have h1 := filtR_measure_lt Cl h
    have h2 := boxCount_le Cl (f a)
    omega
  exact Subrelation.wf (fun {a b} h => key a b h)
    (InvImage.wf (fun a : α => (boxCl Cl).card - boxCount Cl (f a)) Nat.lt_wfRel.wf)

/-! ## 3. The filtered model -/

variable (M : TempModel) (A : TForm)

/-- The subformula-theory of a world: the set of subformulas of `A` true at `u`. -/
noncomputable def theta (u : M.F.W) : Finset TForm :=
  @Finset.filter _ (fun B => M.sat u B) (Classical.decPred _) (subformulas A)

theorem mem_theta {u : M.F.W} {B : TForm} :
    B ∈ theta M A u ↔ B ∈ subformulas A ∧ M.sat u B := by
  simp only [theta, Finset.mem_filter]

theorem theta_subset (u : M.F.W) : theta M A u ⊆ subformulas A := by
  intro B hB; exact (mem_theta M A).1 hB |>.1

/-- The worlds of the filtered model: the *realised* subformula-theories. -/
noncomputable def Wset : Finset (Finset TForm) :=
  @Finset.filter _ (fun S => ∃ u : M.F.W, theta M A u = S) (Classical.decPred _)
    (subformulas A).powerset

theorem mem_Wset {S : Finset TForm} :
    S ∈ Wset M A ↔ S ⊆ subformulas A ∧ ∃ u : M.F.W, theta M A u = S := by
  simp only [Wset, Finset.mem_filter, Finset.mem_powerset]

/-- The world type of the filtered model. -/
def FWorld : Type := {S : Finset TForm // S ∈ Wset M A}

noncomputable instance : Fintype (FWorld M A) := FinsetCoe.fintype _

instance : DecidableEq (FWorld M A) := fun _ _ => decidable_of_iff _ Subtype.ext_iff.symm

/-- The filtered world attached to an original world. -/
noncomputable def thetaW (u : M.F.W) : FWorld M A :=
  ⟨theta M A u, (mem_Wset M A).2 ⟨theta_subset M A u, ⟨u, rfl⟩⟩⟩

theorem exists_rep (S : FWorld M A) : ∃ u : M.F.W, thetaW M A u = S := by
  obtain ⟨-, u, hu⟩ := (mem_Wset M A).1 S.2
  exact ⟨u, Subtype.ext hu⟩

/-- The filtered frame is a genuine temporal Gödel–Löb frame. -/
noncomputable def filtFrame : TempFrame where
  W := FWorld M A
  R := fun S S' => filtR (subformulas A) S.1 S'.1
  T := fun S S' => filtT (subformulas A) S.1 S'.1
  R_trans := fun _ _ _ h₁ h₂ => filtR_trans _ h₁ h₂
  R_wf := filtR_wf (subformulas A) (fun S : FWorld M A => S.1)
  T_refl := by
    intro S
    obtain ⟨u, rfl⟩ := exists_rep M A S
    refine ⟨fun B hB hS => ⟨?_, hS⟩, fun _ _ hS => hS⟩
    have := (mem_theta M A).1 hS
    exact (mem_theta M A).2 ⟨mem_subformulas_glob hB, this.2 u (M.F.T_refl u)⟩
  T_trans := fun _ _ _ h₁ h₂ => filtT_trans _ h₁ h₂
  compat := fun hT hR => filtT_filtR_compat _ hT hR

/-- The filtered valuation: an atom holds at a theory iff it belongs to it. -/
def filtVal : ℕ → (filtFrame M A).W → Prop := fun p S => (TForm.atom p) ∈ S.1

/-- The filtered model. -/
noncomputable def filtModel : TempModel where
  F := filtFrame M A
  V := filtVal M A

/-! ## 4. The truth (filtration) lemma -/


/-! ## 5. The size bound -/


/-! ## 6. Main theorems -/







end TemporalGLDeep


