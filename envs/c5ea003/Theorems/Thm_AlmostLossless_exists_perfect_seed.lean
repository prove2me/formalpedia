-- Prove2me | Theorems.Thm_AlmostLossless_exists_perfect_seed
-- name    : AlmostLossless.exists_perfect_seed
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:16:21.001144+00:00
-- url     : https://prove2.me/theorems/deae82ae-fcf4-42fc-bfda-5fbe303df7a1
-- title:
--   Derandomisation (probabilistic method).
-- statement:
--   **Derandomisation (probabilistic method).**  If the hash range beats the
--   number of ordered pairs of typical words then *some* seed is injective on the
--   whole typical set, and the compressor becomes deterministic with zero failure
--   probability on `T`.
--
--   ```lean
--   theorem AlmostLossless.exists_perfect_seed[Fintype A] [DecidableEq A] [Nonempty A] [Fintype M] [DecidableEq M]
--       [Nonempty M] [DecidableEq S] {h : A → S → M} (hu : TwoUniversal h) (T : Finset S)
--       (hlt : T.offDiag.card < Fintype.card M) :
--       ∃ a : A, ∀ x ∈ T, ∀ y ∈ T, h a x = h a y → x = y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/AlmostLossless/Hashing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AlmostLossless/Hashing.lean#L120

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

theorem AlmostLossless.exists_perfect_seed[Fintype A] [DecidableEq A] [Nonempty A] [Fintype M] [DecidableEq M]
    [Nonempty M] [DecidableEq S] {h : A → S → M} (hu : TwoUniversal h) (T : Finset S)
    (hlt : T.offDiag.card < Fintype.card M) :
    ∃ a : A, ∀ x ∈ T, ∀ y ∈ T, h a x = h a y → x = y := by sorry
