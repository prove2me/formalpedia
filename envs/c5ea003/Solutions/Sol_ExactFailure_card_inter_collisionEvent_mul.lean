-- Prove2me | solution 1 for ExactFailure.card_inter_collisionEvent_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:17:51.180961+00:00
-- url     : https://prove2.me/submissions/98f82c8a-a6dc-4866-8ba9-10df0f6925ee

-- Sol generated from Geometry/ExactFailureMarginal.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessCore
import Definitions.Def_Geometry_ExactFailureMarginal
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
theorem solution{G : Finset (ι → Fin M)} {y x : ι}
    (hG : UnconstrainedAt G y) (hyx : y ≠ x) :
    M * (G ∩ collisionEvent M y x).card = G.card := by
  classical
  have hbij : ((G ∩ collisionEvent M y x) ×ˢ (univ : Finset (Fin M))).card = G.card := by
    apply Finset.card_bij (fun z _ => Function.update z.1 y z.2)
    · rintro ⟨K, v⟩ hz
      exact hG K v (Finset.mem_inter.1 (Finset.mem_product.1 hz).1).1
    · rintro ⟨K, v⟩ hz ⟨K', v'⟩ hz' heq
      have hKc : K y = K x := by
        have := (Finset.mem_inter.1 (Finset.mem_product.1 hz).1).2
        simpa [collisionEvent] using this
      have hKc' : K' y = K' x := by
        have := (Finset.mem_inter.1 (Finset.mem_product.1 hz').1).2
        simpa [collisionEvent] using this
      have hv : v = v' := by
        have := congrArg (fun f => f y) heq
        simpa using this
      have hoff : ∀ a, a ≠ y → K a = K' a := by
        intro a ha
        have := congrArg (fun f => f a) heq
        simpa [Function.update_apply, ha] using this
      have hKK : K = K' := by
        funext a
        rcases eq_or_ne a y with ha | ha
        · rw [ha, hKc, hKc', hoff x (Ne.symm hyx)]
        · exact hoff a ha
      simp [hKK, hv]
    · intro H hH
      refine ⟨(Function.update H y (H x), H y), ?_, ?_⟩
      · refine Finset.mem_product.2 ⟨Finset.mem_inter.2 ⟨hG H (H x) hH, ?_⟩, mem_univ _⟩
        simp only [collisionEvent, mem_filter, mem_univ, true_and]
        rw [Function.update_apply, Function.update_apply, if_pos rfl, if_neg (Ne.symm hyx)]
      · funext a
        rcases eq_or_ne a y with ha | ha
        · rw [ha]; simp
        · simp [ha]
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hbij
  rw [← hbij]; ring
