-- Prove2me | solution 1 for Logic.PhaseRoute.avg_graphInd_mul_additive
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T12:20:53.285993+00:00
-- url     : https://prove2.me/submissions/7545eae3-388e-417c-80bf-d2f98f8fce3c

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
theorem solution {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] [Nonempty α]
    (σ : α ≃ β) (u : α → ℝ) (v : β → ℝ) :
    (avg fun x : α × β => graphInd σ x * additive u v x)
      = ((∑ a, u a) + ∑ b, v b) / ((Fintype.card α : ℝ) * (Fintype.card α : ℝ)) := by
  -- σ forces card β = card α, which is why the published denominator is card α squared.
  have hcard : Fintype.card β = Fintype.card α := (Fintype.card_congr σ).symm
  have step : ∀ a : α, (∑ b : β, graphInd σ (a, b) * additive u v (a, b)) = u a + v (σ a) := by
    intro a; simp [graphInd, additive]
  have hsum : (∑ x : α × β, graphInd σ x * additive u v x) = (∑ a, u a) + ∑ b, v b := by
    rw [Fintype.sum_prod_type, Finset.sum_congr rfl (fun a _ => step a), Finset.sum_add_distrib]
    congr 1
    exact Equiv.sum_comp σ v
  rw [avg, hsum, Fintype.card_prod, Nat.cast_mul, hcard]


