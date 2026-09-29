-- Prove2me | Theorems.Thm_AlmostLossless_avgFailProb_scanCode_le
-- name    : AlmostLossless.avgFailProb_scanCode_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:15:01.266297+00:00
-- url     : https://prove2.me/theorems/8642bbca-7b01-4a54-9f92-73c65355fb4f
-- title:
--   The deliverable bound.
-- statement:
--   **The deliverable bound.**  Draw the seed with a random number generator.
--   The average failure probability of the scan code is at most
--   `ε + |T|(|T|-1)/|M|`, where `ε` bounds the probability of the atypical set: the
--   first term is the (unavoidable) atypicality loss, the second is the Monte-Carlo
--   collision loss.  Every failure is *detected* (the decoder returns `none`).
--
--   ```lean
--   theorem AlmostLossless.avgFailProb_scanCode_le(μ : Source S) (P : ScanScheme S A M)
--       (hu : TwoUniversal P.hash) (ε : ℚ) (hε : 0 ≤ ε) (hT : 1 - ε ≤ μ.prob P.typical) :
--       avgFailProb μ (fun a => P.code a)
--         ≤ ε + (P.typical.offDiag.card : ℚ) / (Fintype.card M : ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/AlmostLossless/Scheme.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AlmostLossless/Scheme.lean#L248

-- Thm stub generated from Logic/AlmostLossless/Scheme.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Core
import Definitions.Def_Logic_AlmostLossless_Hashing
import Definitions.Def_Logic_AlmostLossless_Scheme

/-!
# The Monte-Carlo compressor: hash-and-scan with uniqueness decoding

This file assembles the deliverable of the research thread: an explicit
almost-lossless compression scheme with

* an explicit **failure probability** bound (over the shared random seed and the
  source), see `AlmostLossless.avgFailProb_scanCode_le`;
* an explicit **decoder complexity** figure — the decoder is a single linear
  scan whose cost, counted in hash evaluations, is *exactly* the number of
  candidates it is handed (`AlmostLossless.scanWithCost_cost`), and for the
  bucketed instance the expected number of candidates is at most
  `1 + (|T|-1)/m₁` (`AlmostLossless.expected_bucket_size_le`);
* **no silent corruption**: `AlmostLossless.honest_scanCode` shows the decoder
  is honest *unconditionally* — for every seed, even a catastrophically bad one,
  and for every source word, typical or not.  The uniqueness test built into the
  scan plays the role of a checksum: two candidates means "abort", never a wrong
  answer.

The uniqueness (`ScanState`) decoder is what makes error detection free: the
decoder emits a word only if it is the *unique* candidate matching the received
hash, and the true word is always among the candidates, so an emitted word is
always the true word.
-/

open AlmostLossless

open Finset

/-! ## A cost-instrumented uniqueness scan -/


variable {S A M : Type*}












/-! ## Scan schemes -/


variable [DecidableEq S] [DecidableEq M]







/-! ## Failure probability of the Monte-Carlo scheme -/

variable [Fintype S] [Fintype A] [DecidableEq A] [Nonempty A] [Fintype M] [Nonempty M]

theorem AlmostLossless.avgFailProb_scanCode_le(μ : Source S) (P : ScanScheme S A M)
    (hu : TwoUniversal P.hash) (ε : ℚ) (hε : 0 ≤ ε) (hT : 1 - ε ≤ μ.prob P.typical) :
    avgFailProb μ (fun a => P.code a)
      ≤ ε + (P.typical.offDiag.card : ℚ) / (Fintype.card M : ℚ) := by sorry
