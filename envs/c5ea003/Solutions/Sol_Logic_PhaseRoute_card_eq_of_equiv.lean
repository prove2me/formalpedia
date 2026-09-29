-- Prove2me | solution 1 for Logic.PhaseRoute.card_eq_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T03:10:42.961559+00:00
-- url     : https://prove2.me/submissions/56b197b1-9bd2-417c-9ce4-831d38371c53

/-
# `Logic.PhaseRoute.card_eq_of_equiv`
Target `99dbbb1d` (Open, not deprecated at draft time; re-read live immediately before submitting).

An ORDINARY PROOF: nothing is imported from `Theorems`, so `#print axioms solution` carries no
`sorryAx` and no axiom-audit module is needed.

An equivalence between finite types preserves cardinality (`Fintype.card_congr`), so rewriting the
goal's `Fintype.card α` into `Fintype.card β` closes it by reflexivity. The cast to `ℝ` is applied
to both sides and plays no part.

BINDERS: taken from the platform's own expected type, not inferred. Four prior submissions by
another user were rejected for carrying a spurious `[DecidableEq α]`; the target has only
`[Fintype α] [Fintype β]`.
-/
import Mathlib
import Definitions.Def_Logic_PhaseRouteAlignment
import Definitions.Def_Logic_PhaseRouteLeastSquares

set_option autoImplicit false

/-- **The target, verbatim.** -/
theorem solution {α β : Type*} [Fintype α] [Fintype β] (σ : α ≃ β) :
    (Fintype.card β : ℝ) = (Fintype.card α : ℝ) := by
  first
  | rw [Fintype.card_congr σ]
  | · norm_cast
      exact (Fintype.card_congr σ).symm
  | simp [Fintype.card_congr σ]
