-- Prove2me | solution 1 for AlmostLossless.pairwiseIndependent_dotHash
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T17:07:11.369261+00:00
-- url     : https://prove2.me/submissions/d61a590d-81fb-49cc-862c-d89718093967

-- Sol generated from Logic/AlmostLossless/Hashing.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Hashing
import Theorems.Thm_AlmostLossless_card_ker_mul_card_eq
import Theorems.Thm_AlmostLossless_surjective_dotHom

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
theorem solution: PairwiseIndependent (dotHash p k) := by
  classical
  intro x y hxy
  have hz : x - y ≠ 0 := sub_ne_zero_of_ne hxy
  have hsurj := surjective_dotHom hz
  have hset : #{a : Fin k → ZMod p | dotHash p k a x = dotHash p k a y}
      = #{a : Fin k → ZMod p | dotHom (x - y) a = 0} := by
    apply Finset.card_nbij id
    · intro a ha
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha ⊢
      show dotHom (x - y) a = 0
      have : ∑ i, a i * (x i - y i) = 0 := by
        have hx : ∑ i, a i * x i = ∑ i, a i * y i := ha
        calc ∑ i, a i * (x i - y i) = (∑ i, a i * x i) - ∑ i, a i * y i := by
              rw [← Finset.sum_sub_distrib]; congr 1; ext i; ring
          _ = 0 := by rw [hx, sub_self]
      simpa [dotHom] using this
    · intro a _ b _ hab; exact hab
    · intro a ha
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha ⊢
      refine ⟨a, ?_, rfl⟩
      have : ∑ i, a i * (x i - y i) = 0 := by simpa [dotHom] using ha
      show dotHash p k a x = dotHash p k a y
      have : (∑ i, a i * x i) - ∑ i, a i * y i = 0 := by
        rw [← this, ← Finset.sum_sub_distrib]; congr 1; ext i; ring
      simpa [dotHash, sub_eq_zero] using this
  rw [hset]
  exact card_ker_mul_card_eq (dotHom (x - y)) hsurj
