-- Prove2me | solution 1 for Logic.PhaseRoute.avg_additive
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T11:58:03.311487+00:00
-- url     : https://prove2.me/submissions/78830d24-9b6b-44cb-9116-0ae4991e2db5

/-
# `Logic.PhaseRoute.avg_additive`
Target `37c1e942` (Open; re-read live immediately before submitting).

ORDINARY PROOF — bundle built, closure screens CLEAN. Gift: **SAFE**.

BINDERS — expected type from this target's OWN WA, verbatim (it carries FOUR):
    ∀ {α β} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] (u : α → ℝ) (v : β → ℝ),
      avg (additive u v) = avg u + avg v

DEFINITIONS (read from source):
    avg (f : ι → ℝ)      = (∑ i, f i) / (Fintype.card ι : ℝ)     [LeastSquares:41]
    additive u v         = fun x : α × β => u x.1 + v x.2         [Alignment:79]

MATHS. `additive u v` splits as a first-coordinate lift plus a second-coordinate lift, `avg` is
additive over `Finset.sum`, and each lift averages to the average of its own factor — which is
`avg_comp_fst` and `avg_comp_snd`. Those are separate targets in this bundle, so they are RE-DERIVED
INLINE here: importing them from `Theorems/` would force the reduction path and an axiom audit.

    ∑_{(a,b)} (u a + v b) = ∑_{(a,b)} u a + ∑_{(a,b)} v b = |β|·∑u + |α|·∑v
    avg = (|β|·∑u + |α|·∑v) / (|α|·|β|) = ∑u/|α| + ∑v/|β|

Both nonemptiness hypotheses are load-bearing: each cancellation needs its own cardinality nonzero.

PROBED, NOT GUESSED — `#check`ed in a probe, with four of five step-examples compiling:
  * `Fintype.sum_prod_type (f : α₁ × α₂ → γ) : ∑ x, f x = ∑ x, ∑ y, f (x, y)`
  * `Finset.sum_const (b) : ∑ _x ∈ s, b = #s • b`
  * `Fintype.card_prod (α β) : card (α × β) = card α * card β`
  * `rw [avg]` unfolds directly; the one gap found was `Finset.sum_mul`.
-/
import Mathlib
import Definitions.Def_Logic_PhaseRouteAlignment

set_option autoImplicit false
set_option maxHeartbeats 400000

open Logic.PhaseRoute Finset

open Logic.PhaseRoute in
/-- **The target, verbatim.** -/
theorem solution {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (u : α → ℝ) (v : β → ℝ) :
    avg (additive u v) = avg u + avg v := by
  have hα : (Fintype.card α : ℝ) ≠ 0 := by
    have h : 0 < Fintype.card α := Fintype.card_pos
    positivity
  have hβ : (Fintype.card β : ℝ) ≠ 0 := by
    have h : 0 < Fintype.card β := Fintype.card_pos
    positivity
  have hu : (∑ x : α × β, u x.1) = (Fintype.card β : ℝ) * ∑ a, u a := by
    rw [Fintype.sum_prod_type]
    simp [Finset.sum_const, Finset.card_univ, Finset.sum_mul, mul_comm]
  have hv : (∑ x : α × β, v x.2) = (Fintype.card α : ℝ) * ∑ b, v b := by
    rw [Fintype.sum_prod_type]
    simp [Finset.sum_const, Finset.card_univ]
  have hsplit : (∑ x : α × β, (u x.1 + v x.2))
      = (∑ x : α × β, u x.1) + ∑ x : α × β, v x.2 := Finset.sum_add_distrib
  -- `additive u v` sits UNAPPLIED inside `avg (...)`, so its applied-form equation
  -- lemma has nothing to match: unfold `avg` FIRST to put it under the sum.
  simp only [avg, additive]
  rw [hsplit, hu, hv, Fintype.card_prod, Nat.cast_mul]
  field_simp
