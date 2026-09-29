-- Prove2me | solution 1 for AlmostLossless.card_multiCollision_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:15:17.292956+00:00
-- url     : https://prove2.me/submissions/38e41bff-f251-4cc0-8498-183d605fe631

-- Sol generated from Geometry/AlmostLosslessCore.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessCore
import Theorems.Thm_AlmostLossless_card_collisionEvent_mul
/-
# Almost-lossless (Monte-Carlo) compression: the random-hash core

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

This file develops, from scratch, the counting core of Shannon's random-coding
argument in a purely finitary, `Finset`-based form:

* `AlmostLossless.pigeonhole_barrier` — the exact/all-strings barrier:
  an injective encoder into `Fin M` forces `M ≥ |α|`.
* `AlmostLossless.collisionEvent` — the event `H p = H q` inside the finite
  probability space of *all* codebooks `H : ι → Fin M`.
* `AlmostLossless.card_collisionEvent_mul` — the exact marginal count
  `M * |{H | H p = H q}| = M ^ |ι|` for `p ≠ q`, i.e. the collision
  probability of a fixed pair is exactly `1/M`.
* `AlmostLossless.card_multiCollision_mul_le` — the union bound in counting
  form for an arbitrary finite family of pairs.

Everything is stated with integer arithmetic (no measure theory), so all
probability statements are exact counting identities/inequalities.
-/

open AlmostLossless

open Finset

/-! ## 1. The pigeonhole barrier for exact decoding -/



/-! ## 2. The finite probability space of codebooks

The sample space is the (finite) set of *all* functions `H : ι → Fin M`;
"probability" means normalised counting measure, and we keep everything in the
integers by multiplying through by the total number `M ^ |ι|` of codebooks. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}







open AlmostLossless in
theorem solution(P : Finset (ι × ι)) (hP : ∀ p ∈ P, p.1 ≠ p.2) :
    M * (multiCollision M P).card ≤ P.card * M ^ Fintype.card ι := by
  classical
  have hsub : multiCollision M P ⊆ P.biUnion (fun p => collisionEvent M p.1 p.2) := by
    intro H hH
    simp only [multiCollision, mem_filter, mem_univ, true_and] at hH
    obtain ⟨p, hp, hHp⟩ := hH
    exact mem_biUnion.2 ⟨p, hp, by simp [collisionEvent, hHp]⟩
  have h1 : (multiCollision M P).card ≤ ∑ p ∈ P, (collisionEvent M p.1 p.2).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  calc M * (multiCollision M P).card
      ≤ M * ∑ p ∈ P, (collisionEvent M p.1 p.2).card := Nat.mul_le_mul_left _ h1
    _ = ∑ p ∈ P, M * (collisionEvent M p.1 p.2).card := by rw [Finset.mul_sum]
    _ = ∑ _p ∈ P, M ^ Fintype.card ι :=
        Finset.sum_congr rfl (fun p hp => card_collisionEvent_mul (hP p hp))
    _ = P.card * M ^ Fintype.card ι := by rw [Finset.sum_const, smul_eq_mul]
