-- Prove2me | Theorems.Thm_AlmostLossless_avg_decodeCost_bucketed_le
-- name    : AlmostLossless.avg_decodeCost_bucketed_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:16:36.039887+00:00
-- url     : https://prove2.me/theorems/0a933a42-83a6-467b-be1f-61286c8d1194
-- title:
--   Expected decoder complexity of the bucketed scheme.
-- statement:
--   **Expected decoder complexity of the bucketed scheme.**  Averaged over the
--   random seed, decoding a typical word costs at most `1 + (|T|-1)/m₁` candidate
--   tests — constant on average as soon as the bucket count `m₁` exceeds `|T|`,
--   versus `|T|` for the naive scan and `|S|` for a naive random codebook.
--
--   ```lean
--   theorem AlmostLossless.avg_decodeCost_bucketed_le[Fintype A₁] [DecidableEq A₁] [Nonempty A₁]
--       [Fintype M₁] [Nonempty M₁] (T : Finset S) {h₁ : A₁ → S → M₁} (h₂ : A₂ → S → M₂)
--       (hu₁ : TwoUniversal h₁) (a₂ : A₂) {x : S} (hx : x ∈ T) :
--       (∑ a₁ : A₁, (((bucketed T h₁ h₂).decodeCost (a₁, a₂)
--           ((bucketed T h₁ h₂).hash (a₁, a₂) x) : ℕ) : ℚ)) / (Fintype.card A₁ : ℚ)
--         ≤ 1 + ((T.erase x).card : ℚ) / (Fintype.card M₁ : ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/AlmostLossless/Instances.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AlmostLossless/Instances.lean#L96

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




omit [DecidableEq M₂] in

theorem AlmostLossless.avg_decodeCost_bucketed_le[Fintype A₁] [DecidableEq A₁] [Nonempty A₁]
    [Fintype M₁] [Nonempty M₁] (T : Finset S) {h₁ : A₁ → S → M₁} (h₂ : A₂ → S → M₂)
    (hu₁ : TwoUniversal h₁) (a₂ : A₂) {x : S} (hx : x ∈ T) :
    (∑ a₁ : A₁, (((bucketed T h₁ h₂).decodeCost (a₁, a₂)
        ((bucketed T h₁ h₂).hash (a₁, a₂) x) : ℕ) : ℚ)) / (Fintype.card A₁ : ℚ)
      ≤ 1 + ((T.erase x).card : ℚ) / (Fintype.card M₁ : ℚ) := by sorry
