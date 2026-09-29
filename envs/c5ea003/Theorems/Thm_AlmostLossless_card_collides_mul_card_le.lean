-- Prove2me | Theorems.Thm_AlmostLossless_card_collides_mul_card_le
-- name    : AlmostLossless.card_collides_mul_card_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:15:00.792325+00:00
-- url     : https://prove2.me/theorems/57c126c4-a1e3-4f01-9b01-368969eb1faa
-- title:
--   Union bound over pairs.
-- statement:
--   **Union bound over pairs.**  For a 2-universal family, the number of seeds
--   that are bad for `T` obeys `#bad · |M| ≤ |T.offDiag| · |A|`, where
--   `|T.offDiag| = |T|(|T|-1)` is the number of ordered pairs of distinct typical
--   words.
--
--   ```lean
--   theorem AlmostLossless.card_collides_mul_card_le[Fintype A] [DecidableEq A] [Fintype M] [DecidableEq M]
--       [DecidableEq S] {h : A → S → M} (hu : TwoUniversal h) (T : Finset S) :
--       #{a | CollidesOn h T a} * Fintype.card M ≤ T.offDiag.card * Fintype.card A := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/AlmostLossless/Hashing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AlmostLossless/Hashing.lean#L72

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

theorem AlmostLossless.card_collides_mul_card_le[Fintype A] [DecidableEq A] [Fintype M] [DecidableEq M]
    [DecidableEq S] {h : A → S → M} (hu : TwoUniversal h) (T : Finset S) :
    #{a | CollidesOn h T a} * Fintype.card M ≤ T.offDiag.card * Fintype.card A := by sorry
