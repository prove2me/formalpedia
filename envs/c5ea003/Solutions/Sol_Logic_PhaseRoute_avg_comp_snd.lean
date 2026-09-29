-- Prove2me | solution 1 for Logic.PhaseRoute.avg_comp_snd
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T11:40:54.045617+00:00
-- url     : https://prove2.me/submissions/120165f8-714d-48ec-992e-c7cf778565d2

/-
# `Logic.PhaseRoute.avg_comp_snd`
Target `930aff25` (Open; re-read live immediately before submitting).

ORDINARY PROOF — bundle built, closure screens CLEAN. Gift: **SAFE**.

BINDERS — expected type from this target's OWN WA, verbatim:
    ∀ {α β} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] (g : β → ℝ),
      (avg fun x => g x.2) = avg g
Identical instance list to its mirror `avg_comp_fst` — unusually for this session, the four
PhaseRoute targets all share one signature shape.

MATHS — the mirror of `avg_comp_fst`. Averaging a function of the SECOND coordinate over the product
ignores the first:
    ∑_{(a,b)} g b = ∑_a ∑_b g b = ∑_a (∑_b g b) = |α| · ∑_b g b
and `|α × β| = |α|·|β|` cancels the `|α|`.

The asymmetry with the first-coordinate case is worth noting: there the INNER sum was constant
(`∑_b f a`), here the inner sum is the whole target (`∑_b g b`) and it is the OUTER sum that is
constant. So the two proofs collapse `Finset.sum_const` at different levels, which is why the probe
tested both directions separately — and the second-coordinate example compiled while the
first-coordinate one needed `Finset.sum_mul`.
-/
import Mathlib
import Definitions.Def_Logic_PhaseRouteAlignment

set_option autoImplicit false
set_option maxHeartbeats 400000

open Logic.PhaseRoute Finset

open Logic.PhaseRoute in
/-- **The target, verbatim.** -/
theorem solution {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] (g : β → ℝ) :
    avg (fun x : α × β => g x.2) = avg g := by
  have hα : (Fintype.card α : ℝ) ≠ 0 := by
    have h : 0 < Fintype.card α := Fintype.card_pos
    positivity
  have hβ : (Fintype.card β : ℝ) ≠ 0 := by
    have h : 0 < Fintype.card β := Fintype.card_pos
    positivity
  have hnum : (∑ x : α × β, g x.2) = (Fintype.card α : ℝ) * ∑ b, g b := by
    rw [Fintype.sum_prod_type]
    simp [Finset.sum_const, Finset.card_univ]
  rw [avg, avg, hnum, Fintype.card_prod, Nat.cast_mul]
  field_simp
