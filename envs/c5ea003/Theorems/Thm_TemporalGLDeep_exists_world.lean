-- Prove2me | Theorems.Thm_TemporalGLDeep_exists_world
-- name    : TemporalGLDeep.exists_world
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:55:10.163706+00:00
-- url     : https://prove2.me/theorems/c0b4e0d2-ffe3-44f3-aeae-14cabe28e77b
-- title:
--   Lindenbaum for a finite closure.
-- statement:
--   **Lindenbaum for a finite closure.**  Any consistent hypothesis list is realised by
--   a world of the canonical model, which agrees with the list on all its members.
--
--   ```lean
--   theorem TemporalGLDeep.exists_world(Cl : Finset TForm) (Γ : List TForm) (hΓ : ListCons Γ) :
--       ∃ t, t ∈ CanW Cl ∧ (∀ x ∈ Γ, x ∈ Cl → x ∈ t) ∧ (∀ B : TForm, B.neg ∈ Γ → B ∉ t) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/PosetTheory/TemporalGLCompleteness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/PosetTheory/TemporalGLCompleteness.lean#L94

-- Thm stub generated from Logic/PosetTheory/TemporalGLCompleteness.lean
import Mathlib
import Definitions.Def_Logic_PosetTheory_TemporalGLCompleteness
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

open TemporalGLDeep

open TemporalGL

/-! ## 1. Subformula-closed sets -/





/-! ## 2. Decided subsets and consistency -/

theorem TemporalGLDeep.exists_world(Cl : Finset TForm) (Γ : List TForm) (hΓ : ListCons Γ) :
    ∃ t, t ∈ CanW Cl ∧ (∀ x ∈ Γ, x ∈ Cl → x ∈ t) ∧ (∀ B : TForm, B.neg ∈ Γ → B ∉ t) := by sorry
