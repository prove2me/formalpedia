-- Prove2me | solution 1 for AlmostLossless.avg_collisionCount_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:14:16.407406+00:00
-- url     : https://prove2.me/submissions/98089acb-525c-4947-b75e-b7f2b74659ab

-- Sol generated from Logic/AlmostLossless/Hashing.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Hashing
import Theorems.Thm_AlmostLossless_sum_collisionCount_mul_le

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
theorem solution[Fintype A] [DecidableEq A] [Nonempty A] [Fintype M]
    [DecidableEq M] [Nonempty M] [DecidableEq S] {h : A → S → M} (hu : TwoUniversal h)
    (T : Finset S) (x : S) :
    (∑ a : A, (collisionCount h T a x : ℚ)) / (Fintype.card A : ℚ)
      ≤ ((T.erase x).card : ℚ) / (Fintype.card M : ℚ) := by
  have hA : (0 : ℚ) < (Fintype.card A : ℚ) := by exact_mod_cast Fintype.card_pos (α := A)
  have hM : (0 : ℚ) < (Fintype.card M : ℚ) := by exact_mod_cast Fintype.card_pos (α := M)
  rw [div_le_div_iff₀ hA hM]
  have h1 := sum_collisionCount_mul_le hu T x
  have h2 : ((∑ a : A, collisionCount h T a x : ℕ) : ℚ) * (Fintype.card M : ℚ)
      ≤ ((T.erase x).card : ℚ) * (Fintype.card A : ℚ) := by
    exact_mod_cast h1
  calc (∑ a : A, (collisionCount h T a x : ℚ)) * (Fintype.card M : ℚ)
      = ((∑ a : A, collisionCount h T a x : ℕ) : ℚ) * (Fintype.card M : ℚ) := by push_cast; ring
    _ ≤ ((T.erase x).card : ℚ) * (Fintype.card A : ℚ) := h2
