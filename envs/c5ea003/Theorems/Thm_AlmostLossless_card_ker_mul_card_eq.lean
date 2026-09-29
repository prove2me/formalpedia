-- Prove2me | Theorems.Thm_AlmostLossless_card_ker_mul_card_eq
-- name    : AlmostLossless.card_ker_mul_card_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:16:15.074682+00:00
-- url     : https://prove2.me/theorems/15de9e06-a61b-4932-adee-df4eeb5dfdfc
-- title:
--   All fibres of a surjective additive homomorphism between finite abelian
-- statement:
--   All fibres of a surjective additive homomorphism between finite abelian
--   groups have the same size; in particular the kernel has size `|A|/|M|`.
--
--   ```lean
--   theorem AlmostLossless.card_ker_mul_card_eq{A M : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
--       [AddCommGroup M] [Fintype M] [DecidableEq M] (f : A →+ M) (hf : Function.Surjective f) :
--       #{a | f a = 0} * Fintype.card M = Fintype.card A := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/AlmostLossless/Hashing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AlmostLossless/Hashing.lean#L263

-- Thm stub generated from Logic/AlmostLossless/Hashing.lean
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

theorem AlmostLossless.card_ker_mul_card_eq{A M : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    [AddCommGroup M] [Fintype M] [DecidableEq M] (f : A →+ M) (hf : Function.Surjective f) :
    #{a | f a = 0} * Fintype.card M = Fintype.card A := by sorry
