-- Prove2me | solution 1 for AlmostLossless.card_ker_mul_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:28:57.362064+00:00
-- url     : https://prove2.me/submissions/faa2d83e-ed55-4801-96f9-681ea2985ba8

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
theorem solution{A M : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    [AddCommGroup M] [Fintype M] [DecidableEq M] (f : A →+ M) (hf : Function.Surjective f) :
    #{a | f a = 0} * Fintype.card M = Fintype.card A := by
  have h1 : Fintype.card A = ∑ c : M, #{a | f a = c} := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun a _ => Finset.mem_univ (f a))
  have h2 : ∀ c : M, #{a | f a = c} = #{a | f a = 0} :=
    fun c => AddMonoidHom.card_fiber_eq_of_mem_range f (hf c) ⟨0, by simp⟩
  rw [h1]
  simp [h2, Finset.sum_const, mul_comm]
