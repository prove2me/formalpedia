-- Prove2me | solution 1 for ExactFailure.failure_prob_le_shannon
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:21:31.793234+00:00
-- url     : https://prove2.me/submissions/824ab3dc-0431-4f89-a840-0bcb27c1818c

-- Sol generated from Geometry/ExactFailureMarginal.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Definitions.Def_Geometry_ExactFailureMarginal
import Theorems.Thm_ExactFailure_failure_prob_exact
/-
# Which marginals?  The exact failure law of the random codebook

Research thread *Compression Beyond the Pigeonhole Bound*, cycle v19c.

`Geometry.AlmostLosslessConverse` obtains `P[failure] ≥ k/(2M)` (for `2(k-1) ≤ M`)
by feeding two marginals into the Bonferroni inequality, and
`Geometry.BonferroniMarginals` improves this to the unconditional `k/(M+k-1)` by
feeding the *same* two marginals into the second-moment inequality.  Both are
lower bounds.  This file closes the question completely: the failure probability
of the uniform random codebook is *computed exactly*,

`P[failure] = 1 - (1 - 1/M)^k`,   `k = |S \ {x}|`,

and both the Shannon upper bound and a matching lower bound are then elementary
consequences.  The mechanism is a **conditional marginal principle**: the
collision event `H y = H x` has probability exactly `1/M` *conditionally on any
event that does not constrain the coordinate `y`*.  That is the precise sense in
which the almost-lossless analysis is a statement about marginals.

Main results.

* `ExactFailure.card_inter_collisionEvent_mul` — the **conditional collision
  marginal**: `M · |G ∩ {H : H y = H x}| = |G|` for every `G` unconstrained at
  `y` (`y ≠ x`).  A strict generalisation of
  `AlmostLossless.card_collisionEvent_mul` (take `G = univ`).
* `ExactFailure.card_noCollisionEvent_mul` — by induction along the competitors:
  `M^k · |{H : H y ≠ H x for all y ∈ D}| = (M-1)^k · M^{|α|}`, `k = |D|`.
* `ExactFailure.card_failSet_exact` — the **exact failure count**
  `M^k · |failSet| + (M-1)^k · M^{|α|} = M^k · M^{|α|}`.
* `ExactFailure.failure_prob_exact` — `P[failure] = 1 - (1 - 1/M)^k`.
* `ExactFailure.failure_prob_le_shannon` — recovers the random-coding bound
  `P[failure] ≤ k/M` (`AlmostLossless.failSet_prob_le`) from the exact law.
* `ExactFailure.failure_prob_ge_harmonic` — the matching lower bound
  `P[failure] ≥ k/(M+k)`, proved from the exact law by Bernoulli's inequality.
  Together the two show `P[failure] = Θ(k/M)` for **all** `k` and `M`.
-/

open ExactFailure

open Finset AlmostLossless

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}

/-! ## 1. The conditional collision marginal -/



/-! ## 2. The no-collision event and its exact count -/





/-! ## 3. The exact failure law of the almost-lossless scheme -/

variable {α : Type*} [Fintype α] [DecidableEq α]




/-! ## 4. Matching upper and lower bounds from the exact law -/



/-! ## 5. Lab notes: brute-force confirmation of the exact law

The exact law predicts `|failSet| = M^{|α|} - (M-1)^k · M^{|α| - k}` with
`k = |α| - 1` when every other string is a competitor.  Two independent
brute-force enumerations of the full codebook space, checked by the kernel:
`|α| = 3, M = 2` gives `8 - 1·2 = 6`, and `|α| = 4, M = 3` gives `81 - 8·3 = 57`. -/




open ExactFailure in
theorem solution(S : Finset α) (x : α) (hM : 0 < M) :
    ((failSet S x M).card : ℝ) / ((M : ℝ) ^ Fintype.card α)
      ≤ (S.erase x).card / (M : ℝ) := by
  classical
  set k := (S.erase x).card with hk
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  rw [failure_prob_exact S x hM]
  have hber : 1 + (k : ℝ) * (-(1 / (M : ℝ))) ≤ (1 + -(1 / (M : ℝ))) ^ k := by
    apply one_add_mul_le_pow
    have : 1 / (M : ℝ) ≤ 1 := by
      rw [div_le_one hMpos]; linarith
    linarith
  have hrw : (1 : ℝ) - 1 / (M : ℝ) = 1 + -(1 / (M : ℝ)) := by ring
  rw [hrw]
  have hkM : (k : ℝ) * (1 / (M : ℝ)) = (k : ℝ) / (M : ℝ) := by ring
  linarith [hber]
