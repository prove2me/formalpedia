-- Prove2me | solution 1 for Logic.PhaseRoute.avg_mul_additive_of_zero_marginals
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T12:02:40.663135+00:00
-- url     : https://prove2.me/submissions/a02fe7d6-bd08-4e6b-b103-25f51775cf78

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
import Definitions.Def_Logic_PhaseRouteANOVA

set_option autoImplicit false
set_option maxHeartbeats 400000

open Logic.PhaseRoute Finset

open Logic.PhaseRoute in
/-- **The target, verbatim.** -/
theorem solution {α β : Type*} [Fintype α] [Fintype β] {g : α × β → ℝ}
    (hrow : ∀ a, (∑ b : β, g (a, b)) = 0) (hcol : ∀ b, (∑ a : α, g (a, b)) = 0)
    (u : α → ℝ) (v : β → ℝ) :
    avg (fun x : α × β => g x * additive u v x) = 0 := by
  -- No `Nonempty` anywhere: the grand sum is 0, and `0 / N = 0` for EVERY N, including 0.
  have hsum : (∑ x : α × β, g x * additive u v x) = 0 := by
    rw [Fintype.sum_prod_type]
    have step : ∀ a : α, (∑ b : β, g (a, b) * additive u v (a, b))
        = (∑ b : β, g (a, b)) * u a + ∑ b : β, g (a, b) * v b := by
      intro a
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun b _ => by simp only [additive]; ring)
    simp only [step, hrow, zero_mul, zero_add]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hcol, zero_mul, Finset.sum_const_zero]
  simp only [avg, hsum, zero_div]


