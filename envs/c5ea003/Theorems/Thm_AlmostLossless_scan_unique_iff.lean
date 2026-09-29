-- Prove2me | Theorems.Thm_AlmostLossless_scan_unique_iff
-- name    : AlmostLossless.scan_unique_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:15:47.69173+00:00
-- url     : https://prove2.me/theorems/8c9f3e55-11c7-4905-8188-35010ecb38cc
-- title:
--   A scan reports a unique answer exactly when the candidate list contains
-- statement:
--   A scan reports a unique answer exactly when the candidate list contains
--   exactly one match; this is the error-detection guarantee.
--
--   ```lean
--   theorem AlmostLossless.scan_unique_iff(p : S → Bool) (L : List S) (t : S) :
--       scan p L = .unique t ↔ L.filter p = [t] := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/AlmostLossless/Scheme.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AlmostLossless/Scheme.lean#L101

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

theorem AlmostLossless.scan_unique_iff(p : S → Bool) (L : List S) (t : S) :
    scan p L = .unique t ↔ L.filter p = [t] := by sorry
