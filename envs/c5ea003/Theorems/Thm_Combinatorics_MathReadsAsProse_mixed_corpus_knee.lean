-- Prove2me | Theorems.Thm_Combinatorics_MathReadsAsProse_mixed_corpus_knee
-- name    : Combinatorics.MathReadsAsProse.mixed_corpus_knee
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:08:30.54301+00:00
-- url     : https://prove2.me/theorems/d4007727-e9d1-4fa3-b62a-960af88163cb
-- title:
--   Corpus mixing cannot break the shared entry.
-- statement:
--   **Corpus mixing cannot break the shared entry.**  Any mixture of the prose
--   and mathematical-text sweeps has its knee at `16` as well: mixing is trapped
--   between the two constituent knees, which coincide.  This closes barrier (c)
--   ("one corpus mix"): the reported number is stable under the mixing ratio.
--
--   ```lean
--   theorem Combinatorics.MathReadsAsProse.mixed_corpus_knee{theta g : ℚ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
--       (hlo : (979 : ℚ) / 1000 < g) (hhi : g ≤ (987 : ℚ) / 1000) :
--       knee (mixCurve theta proseWorkload512.agree mathWorkload512.agree) g = 16 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/MathReadsAsProse.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/MathReadsAsProse.lean#L257

-- Thm stub generated from Combinatorics/MathReadsAsProse.lean
import Mathlib
import Definitions.Def_Combinatorics_KneeInvariance
import Definitions.Def_Combinatorics_MathReadsAsProse

/-!
# MATH-READS-AS-PROSE: the measured NET-70 instance

This file instantiates the abstract theory of `Combinatorics.KneeInvariance` on
the **measured NET-70 sweep** and derives the verdict formally.

Measured data (Qwen-class model, exact gate, 24 windows per cell, deterministic
harness; the harness is byte-identical across domains, only the text changes):

| ctx  | domain | sweep (budget ↦ retained agreement)                              | full acc |
|------|--------|------------------------------------------------------------------|----------|
| 512  | math   | 4 ↦ .907, 8 ↦ .959, 12 ↦ .979, 16 ↦ .987, 20 ↦ .989, 24 ↦ .988   | .3262    |
| 512  | prose  | knee at 16 (NET-6x)                                              | .4460    |
| 1024 | math   | 8 ↦ .952, 12 ↦ .965, 16 ↦ .978, 20 ↦ .983, 24+ ↦ pass            | .3418    |
| 1024 | prose  | knee at 20 (NET-6x)                                              | .4612    |

Two modelling decisions, both stated explicitly:

* the sweep is read as a **monotone step count profile** on `n = 10000`
  windows — the measured `24 ↦ .988` at ctx 512 sits below `20 ↦ .989` by one
  unit in the third decimal, i.e. inside the reported standard error, so the
  monotone hull (`.989` from 20 on) is used;
* at `k = ctx` the truncated model *is* the full model, so the profile
  saturates at `1` there.  This is what makes every gate `≤ 1` reachable.

Everything else is derived.  In particular the knees are *computed*, not
assumed: `math512_knee = 16` and `math1024_knee = 20`, for **every** gate in the
measured admissible windows `(0.979, 0.987]` and `(0.978, 0.983]`.  Those
windows overlap in `(0.979, 0.983]`, so one single gate certifies both cells and
the ctx increment is exactly `+4` (NET-67 shape preservation).

The verdict theorems are `math_reads_as_prose_512`, `math_reads_as_prose_1024`
(P3: identical knees with a 12-point accuracy gap), `net70_P1_refuted`
(harder text does not need more keys) and `three_domain_deployment_table`
(prose and math share one deployment entry; only code shifts).
-/

open Combinatorics.MathReadsAsProse

open Finset Combinatorics.KneeInvariance

/-! ## The measured count profiles -/













/-! ## The measured workloads -/






/-! ## The knees are computed, over the whole admissible gate window -/










/-! ## The verdict -/





/-! ## The three-domain deployment table -/

theorem Combinatorics.MathReadsAsProse.mixed_corpus_knee{theta g : ℚ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hlo : (979 : ℚ) / 1000 < g) (hhi : g ≤ (987 : ℚ) / 1000) :
    knee (mixCurve theta proseWorkload512.agree mathWorkload512.agree) g = 16 := by sorry
