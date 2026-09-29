-- Prove2me | Theorems.Thm_AlmostLossless_avg_collisionCount_le
-- name    : AlmostLossless.avg_collisionCount_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:16:02.336158+00:00
-- url     : https://prove2.me/theorems/65e86c15-1685-44c5-857e-ef7598631f7e
-- title:
--   Expected decoder work.
-- statement:
--   **Expected decoder work.**  Averaged over the random seed, the number of
--   false candidates competing with a typical word `x` is at most `(|T|-1)/|M|`.
--   A bucketed decoder therefore tests `1 + (|T|-1)/|M|` candidates on average,
--   instead of the `|T|` of a naive linear scan.
--
--   ```lean
--   theorem AlmostLossless.avg_collisionCount_le[Fintype A] [DecidableEq A] [Nonempty A] [Fintype M]
--       [DecidableEq M] [Nonempty M] [DecidableEq S] {h : A → S → M} (hu : TwoUniversal h)
--       (T : Finset S) (x : S) :
--       (∑ a : A, (collisionCount h T a x : ℚ)) / (Fintype.card A : ℚ)
--         ≤ ((T.erase x).card : ℚ) / (Fintype.card M : ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/AlmostLossless/Hashing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AlmostLossless/Hashing.lean#L176

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

theorem AlmostLossless.avg_collisionCount_le[Fintype A] [DecidableEq A] [Nonempty A] [Fintype M]
    [DecidableEq M] [Nonempty M] [DecidableEq S] {h : A → S → M} (hu : TwoUniversal h)
    (T : Finset S) (x : S) :
    (∑ a : A, (collisionCount h T a x : ℚ)) / (Fintype.card A : ℚ)
      ≤ ((T.erase x).card : ℚ) / (Fintype.card M : ℚ) := by sorry
