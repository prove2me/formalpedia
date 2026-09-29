-- Prove2me | solution 1 for Logic.PhaseRoute.varr_graphInd_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T12:40:38.045696+00:00
-- url     : https://prove2.me/submissions/ff961171-ec81-4e74-b020-115143668b9f

/-
# `Logic.PhaseRoute.varr_graphInd_pos`
Target `79bf50d7` (Open; re-read live before submitting).

BINDERS — from this target's OWN WA, verbatim: [DecidableEq β] and [Nonempty α], NO [Nonempty β].

MATHS. `graphInd σ` is the indicator of the graph of σ, hence idempotent, and every row sums to 1.
So both ∑ graphInd and ∑ graphInd² equal card α. σ forces card β = card α, so the product space has
card α ² points and BOTH averages are 1/card α. Therefore varr = 1/c − 1/c² = (c−1)/c², which is
positive exactly when c ≥ 2 — the hypothesis `hcard`.

NOTE: `field_simp` CLOSES `hrw` on its own; a trailing `ring` errors with "No goals to be solved".
This is the sixth instance tonight of that trap, in both directions — there is no rule, only testing.
-/
import Mathlib
import Definitions.Def_Logic_PhaseRouteAlignment
import Definitions.Def_Logic_PhaseRouteLeastSquares

set_option autoImplicit false
set_option maxHeartbeats 400000

open Logic.PhaseRoute Finset

open Logic.PhaseRoute in
/-- **The target, verbatim.** -/
theorem solution {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] [Nonempty α]
    (σ : α ≃ β) (hcard : 2 ≤ Fintype.card α) : 0 < varr (graphInd σ) := by
  have hcb : Fintype.card β = Fintype.card α := (Fintype.card_congr σ).symm
  have hc2 : (2 : ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast hcard
  have hc0 : (Fintype.card α : ℝ) ≠ 0 := by linarith
  have h1 : (∑ x : α × β, graphInd σ x) = (Fintype.card α : ℝ) := by
    rw [Fintype.sum_prod_type,
      Finset.sum_congr rfl (fun a _ => (by simp [graphInd] : (∑ b : β, graphInd σ (a, b)) = 1)),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have h2 : (∑ x : α × β, graphInd σ x * graphInd σ x) = (Fintype.card α : ℝ) := by
    rw [Fintype.sum_prod_type,
      Finset.sum_congr rfl
        (fun a _ => (by simp [graphInd] :
          (∑ b : β, graphInd σ (a, b) * graphInd σ (a, b)) = 1)),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [varr, cov, avg, avg, h1, h2, Fintype.card_prod, Nat.cast_mul, hcb]
  have hrw : (Fintype.card α : ℝ) / ((Fintype.card α : ℝ) * (Fintype.card α : ℝ))
      - (Fintype.card α : ℝ) / ((Fintype.card α : ℝ) * (Fintype.card α : ℝ))
        * ((Fintype.card α : ℝ) / ((Fintype.card α : ℝ) * (Fintype.card α : ℝ)))
      = ((Fintype.card α : ℝ) - 1) / ((Fintype.card α : ℝ) * (Fintype.card α : ℝ)) := by
    field_simp
  rw [hrw]
  apply div_pos
  · linarith
  · positivity
