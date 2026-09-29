-- Prove2me | solution 1 for Logic.PhaseRoute.avg_graphInd
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T03:15:12.219687+00:00
-- url     : https://prove2.me/submissions/e8aab302-e2af-4439-9c85-da3e75797148

/-
# `Logic.PhaseRoute.avg_graphInd`
Target `72b0158c` (Open, not deprecated at draft time; re-read live immediately before submitting).

An ORDINARY PROOF: nothing is imported from `Theorems`, so `#print axioms solution` carries no
`sorryAx` and no axiom-audit module is needed.

`graphInd σ` is the indicator of the graph of `σ` inside `α × β`, and `avg` divides a sum over the
whole index type by its cardinality. Summing the indicator over `α × β` fires exactly once for each
`a` (at `b = σ a`), giving `card α`. The denominator is `card (α × β) = card α * card β`, and `σ`
forces `card β = card α`, so the quotient collapses to `1 / card α`. That last step needs
`card α ≠ 0`, which is exactly what the `[Nonempty α]` binder supplies.

BINDERS: taken from the platform's own expected type, not inferred. `DecidableEq` is on β (the
indicator compares in β) and `Nonempty` only on α.
-/
import Mathlib
import Definitions.Def_Logic_PhaseRouteAlignment
import Definitions.Def_Logic_PhaseRouteLeastSquares

set_option autoImplicit false

open Logic.PhaseRoute in
/-- **The target, verbatim.** -/
theorem solution {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] [Nonempty α] (σ : α ≃ β) :
    avg (graphInd σ) = 1 / (Fintype.card α : ℝ) := by
  classical
  have hcard : Fintype.card β = Fintype.card α := (Fintype.card_congr σ).symm
  have hpos : 0 < Fintype.card α := Fintype.card_pos
  have hne : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hsum : (∑ x : α × β, graphInd σ x) = (Fintype.card α : ℝ) := by
    rw [Fintype.sum_prod_type]
    first
    | simp [graphInd]
    | · simp only [graphInd]
        rw [Finset.sum_congr rfl (fun a _ => Finset.sum_ite_eq' Finset.univ (σ a) (fun _ => (1:ℝ)))]
        simp
  show (∑ x : α × β, graphInd σ x) / (Fintype.card (α × β) : ℝ) = 1 / (Fintype.card α : ℝ)
  rw [hsum, Fintype.card_prod, hcard]
  push_cast
  first
  | · rw [div_eq_div_iff (by positivity) hne]
      ring
  | field_simp
  | · field_simp
      ring
