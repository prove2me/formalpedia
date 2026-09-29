-- Prove2me | solution 1 for AlmostLossless.sum_collisionCount_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:12:27.041612+00:00
-- url     : https://prove2.me/submissions/dc7a00c7-66dc-418a-baa6-8795e6c7ac68

-- Sol generated from Logic/AlmostLossless/Hashing.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Hashing

/-!
# Two-universal hash families: the derandomised random codebook

Shannon's random-coding argument draws a codebook uniformly at random.  For
*almost-lossless source coding* the only property of the random codebook that
is ever used is that two fixed distinct source words collide with probability
`≤ 1/|M|`.  That is exactly **2-universality**, and it can be achieved by a
family whose seed is `k` field elements and whose evaluation costs `k`
multiplications — an honest "random number generator" with an explicit
complexity figure, as opposed to an exponentially large random codebook.

## Contents

* `AlmostLossless.TwoUniversal` : the defining counting inequality.
* `AlmostLossless.card_collides_mul_card_le` : union bound over the `|T|(|T|-1)`
  ordered pairs of a typical set `T`, giving
  `#{bad seeds} · |M| ≤ |T.offDiag| · |A|`.
* `AlmostLossless.collisionProb_le` : probability form, `P(bad seed) ≤
  |T.offDiag| / |M|`; the Monte-Carlo failure bound of the scheme.
* `AlmostLossless.exists_perfect_seed` : **derandomisation by the probabilistic
  method** — if `|M| > |T|(|T|-1)` then some seed is injective on the whole
  typical set, so the randomness can be removed entirely.
* `AlmostLossless.twoUniversal_dotHash` : a concrete instance, the inner-product
  family `h_a(x) = ∑ a i * x i` over `ZMod p`, proved 2-universal from the
  fact that a nonzero linear functional on `(ZMod p)^k` has all fibres of the
  same size.
-/

open AlmostLossless

open Finset

variable {S A M : Type*}

/-! ## Two-universality -/










/-! ## Expected number of false candidates (decoder work) -/




/-! ## Products of hash families -/


/-! ## A concrete 2-universal family: inner products over `ZMod p` -/


variable {p k : ℕ} [Fact p.Prime]









open AlmostLossless in
theorem solution[Fintype A] [DecidableEq A] [Fintype M] [DecidableEq M]
    [DecidableEq S] {h : A → S → M} (hu : TwoUniversal h) (T : Finset S) (x : S) :
    (∑ a : A, collisionCount h T a x) * Fintype.card M
      ≤ (T.erase x).card * Fintype.card A := by
  classical
  have key : ∑ a : A, collisionCount h T a x
      = ∑ y ∈ T.erase x, #{a | h a y = h a x} := by
    unfold collisionCount
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [key, Finset.sum_mul]
  calc ∑ y ∈ T.erase x, #{a | h a y = h a x} * Fintype.card M
      ≤ ∑ _y ∈ T.erase x, Fintype.card A := by
        refine Finset.sum_le_sum ?_
        intro y hy
        exact hu y x (Finset.ne_of_mem_erase hy)
    _ = (T.erase x).card * Fintype.card A := by rw [Finset.sum_const, smul_eq_mul]
