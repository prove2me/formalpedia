-- Prove2me | Theorems.Thm_AlmostLossless_card_bucket_eq
-- name    : AlmostLossless.card_bucket_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:15:46.419576+00:00
-- url     : https://prove2.me/theorems/abc93f9b-e702-4eaa-81d4-056d714af83f
-- title:
--   The size of a bucket containing the typical word `x`: one true candidate
-- statement:
--   The size of a bucket containing the typical word `x`: one true candidate
--   plus the false candidates counted by `collisionCount`.
--
--   ```lean
--   theorem AlmostLossless.card_bucket_eq(T : Finset S) (h₁ : A₁ → S → M₁) (a₁ : A₁) {x : S} (hx : x ∈ T) :
--       #{t ∈ T | h₁ a₁ t = h₁ a₁ x} = 1 + collisionCount h₁ T a₁ x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/AlmostLossless/Instances.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AlmostLossless/Instances.lean#L64

-- Thm stub generated from Logic/AlmostLossless/Instances.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Hashing
import Definitions.Def_Logic_AlmostLossless_Instances
import Definitions.Def_Logic_AlmostLossless_Scheme

/-!
# Instances: linear scan, bucketed scan, and a concrete `ZMod p` compressor

Two instances of `AlmostLossless.ScanScheme`:

* `AlmostLossless.linearScan` — the decoder scans the whole typical set:
  cost exactly `|T|` hash evaluations, deterministic worst case.
* `AlmostLossless.bucketed` — the codeword is a pair (bucket hash, checksum
  hash) and the decoder scans only one bucket, taken from a precomputed index
  of `T`.  Its cost when decoding a typical word `x` is exactly
  `1 + collisionCount`, and the *expected* cost over the random seed is at most
  `1 + (|T|-1)/m₁` (`AlmostLossless.avg_decodeCost_bucketed_le`): the decoder
  becomes essentially constant-time once `m₁ ≳ |T|`, while the transmitted rate
  is `log m₁ + log m₂` bits.

Finally `AlmostLossless.zmod_scheme` packages the whole pipeline over
`(ZMod p)^k` with the inner-product hash family: `k` field symbols are
compressed to *one* symbol plus a failure flag, the decoder is honest for every
seed, its cost is exactly `|T|`, and the average failure probability is at most
`ε + |T|(|T|-1)/p`.  The companion statement
`AlmostLossless.zmod_uniform_hopeless` shows this is no contradiction with the
pigeonhole bound: on the *uniform* source the very same alphabet fails with
probability at least `1 - (p+1)/p^k`.
-/

open AlmostLossless

open Finset

variable {S A M : Type*} [DecidableEq S] [DecidableEq M]

/-! ## The linear-scan scheme -/



/-! ## The bucketed scheme -/


variable {A₁ A₂ M₁ M₂ : Type*} [DecidableEq M₁] [DecidableEq M₂]

theorem AlmostLossless.card_bucket_eq(T : Finset S) (h₁ : A₁ → S → M₁) (a₁ : A₁) {x : S} (hx : x ∈ T) :
    #{t ∈ T | h₁ a₁ t = h₁ a₁ x} = 1 + collisionCount h₁ T a₁ x := by sorry
