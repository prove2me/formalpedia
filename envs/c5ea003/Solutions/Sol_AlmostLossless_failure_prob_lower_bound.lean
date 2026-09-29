-- Prove2me | solution 1 for AlmostLossless.failure_prob_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:38:18.047617+00:00
-- url     : https://prove2.me/submissions/c0a1624d-f620-46a7-ba30-41e3f2e85a82

-- Sol generated from Geometry/AlmostLosslessConverse.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessCore
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Theorems.Thm_AlmostLossless_card_collisionEvent_mul
import Theorems.Thm_AlmostLossless_card_doubleCollision_mul_le
import Theorems.Thm_AlmostLossless_card_sum_le_card_biUnion_add_offDiag
import Theorems.Thm_AlmostLossless_failSet_eq_biUnion
/-
# How far beyond the pigeonhole bound can one go?  Converse and tightness

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

Two adversarial questions about the almost-lossless scheme of
`Geometry.AlmostLosslessDecoder`:

1. *How much can the counting bound really be relaxed?*
   `AlmostLossless.converse_card_good_le` — **the ε-relaxed pigeonhole bound**:
   for **any** encoder/decoder pair whatsoever, the set of strings decoded
   correctly has size at most `M`.  So a `(1-ε)`-reliable code for a typical set
   `S` still needs `M ≥ (1-ε)|S|`: relaxation buys a factor `(1-ε)`, no more.

2. *Is the `1/ε` overhead of random hashing an artefact of the union bound?*
   No.  `AlmostLossless.failure_prob_lower_bound` is a **Bonferroni lower bound**
   on the failure probability of uniform random hashing:
   `P[failure] ≥ (|S|-1) / (2M)` once `2(|S|-2) ≤ M`.
   Hence uniform random hashing genuinely needs `M ≳ |S| / ε`, a factor `Θ(1/ε)`
   above the converse — the gap is a property of the *random codebook*, not of
   the analysis.

Supporting combinatorics proved here from scratch:
* `AlmostLossless.card_sum_le_card_biUnion_add_offDiag` — the second Bonferroni
  inequality for an arbitrary finite family of finite sets.
* `AlmostLossless.card_doubleCollision_mul_le` — a two-coordinate refinement of
  the marginal count of `AlmostLosslessCore`: two prescribed collisions have
  probability `1/M²`.
-/

open AlmostLossless

open Finset

/-! ## 1. The ε-relaxed pigeonhole bound (converse) -/



/-! ## 2. Bonferroni: a lower bound for unions of finite sets -/


/-! ## 3. Two prescribed collisions have probability `1/M²` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}


/-! ## 4. The failure probability of random hashing is genuinely `≍ |S|/M` -/

variable {α : Type*} [Fintype α] [DecidableEq α]





open AlmostLossless in
theorem solution(S : Finset α) (x : α) :
    (S.erase x).card * M * M ^ Fintype.card α
      ≤ M ^ 2 * (failSet S x M).card
        + (S.erase x).offDiag.card * M ^ Fintype.card α := by
  classical
  set D := S.erase x with hD
  set N := M ^ Fintype.card α with hN
  have hbon := card_sum_le_card_biUnion_add_offDiag (fun y => collisionEvent M y x) D
  -- multiply the Bonferroni inequality by `M²`
  have hleft : M ^ 2 * ∑ y ∈ D, (collisionEvent M y x).card = D.card * M * N := by
    have : ∀ y ∈ D, M * (collisionEvent M y x).card = N := by
      intro y hy
      exact card_collisionEvent_mul (Finset.mem_erase.1 hy).1
    calc M ^ 2 * ∑ y ∈ D, (collisionEvent M y x).card
        = ∑ y ∈ D, M * (M * (collisionEvent M y x).card) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun y _ => by ring)
      _ = ∑ _y ∈ D, M * N := Finset.sum_congr rfl (fun y hy => by rw [this y hy])
      _ = D.card * M * N := by rw [Finset.sum_const, smul_eq_mul]; ring
  have hright : ∀ p ∈ D.offDiag,
      M ^ 2 * ((collisionEvent M p.1 x) ∩ (collisionEvent M p.2 x)).card ≤ N := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    exact card_doubleCollision_mul_le hp.2.2 (Finset.mem_erase.1 hp.1).1
      (Finset.mem_erase.1 hp.2.1).1
  calc D.card * M * N = M ^ 2 * ∑ y ∈ D, (collisionEvent M y x).card := hleft.symm
    _ ≤ M ^ 2 * ((D.biUnion (fun y => collisionEvent M y x)).card
          + ∑ p ∈ D.offDiag, ((collisionEvent M p.1 x) ∩ (collisionEvent M p.2 x)).card) :=
        Nat.mul_le_mul_left _ hbon
    _ = M ^ 2 * (failSet S x M).card
          + ∑ p ∈ D.offDiag, M ^ 2 *
              ((collisionEvent M p.1 x) ∩ (collisionEvent M p.2 x)).card := by
        rw [Nat.mul_add, failSet_eq_biUnion, Finset.mul_sum]
    _ ≤ M ^ 2 * (failSet S x M).card + ∑ _p ∈ D.offDiag, N :=
        Nat.add_le_add_left (Finset.sum_le_sum hright) _
    _ = M ^ 2 * (failSet S x M).card + D.offDiag.card * N := by
        rw [Finset.sum_const, smul_eq_mul]
