-- Prove2me | Theorems.Thm_AlmostLossless_injOn_of_not_collidesOn
-- name    : AlmostLossless.injOn_of_not_collidesOn
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:14:54.354958+00:00
-- url     : https://prove2.me/theorems/6731d62b-6ec9-41d9-955f-98f1801883f7
-- title:
--   A good seed hashes the typical set injectively: this is precisely what makes
-- statement:
--   A good seed hashes the typical set injectively: this is precisely what makes
--   the decoder's answer unique, hence correct.
--
--   ```lean
--   theorem AlmostLossless.injOn_of_not_collidesOn[DecidableEq S] [DecidableEq M] {h : A → S → M}
--       {T : Finset S} {a : A} (ha : ¬ CollidesOn h T a) :
--       ∀ x ∈ T, ∀ y ∈ T, h a x = h a y → x = y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/AlmostLossless/Hashing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AlmostLossless/Hashing.lean#L63

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

theorem AlmostLossless.injOn_of_not_collidesOn[DecidableEq S] [DecidableEq M] {h : A → S → M}
    {T : Finset S} {a : A} (ha : ¬ CollidesOn h T a) :
    ∀ x ∈ T, ∀ y ∈ T, h a x = h a y → x = y := by sorry
