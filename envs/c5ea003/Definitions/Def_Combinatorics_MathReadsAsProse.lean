-- Prove2me | Definitions.Def_Combinatorics_MathReadsAsProse
-- name    : Combinatorics_MathReadsAsProse
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:31:23.238356+00:00
-- url     : https://prove2.me/theorems/a3e8ebc3-82d7-4d0e-acfd-cd9f59df399a
-- title:
--   Aether Catalog definitions — Combinatorics_MathReadsAsProse
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.MathReadsAsProse`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/MathReadsAsProse.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_KneeInvariance

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

namespace Combinatorics.MathReadsAsProse

open Finset Combinatorics.KneeInvariance

/-! ## The measured count profiles -/

/-- Number of served windows out of `10000` at budget `k`, mathematical text,
ctx 512. -/
def mathT512 (k : ℕ) : ℕ :=
  if k < 4 then 0
  else if k < 8 then 9070
  else if k < 12 then 9590
  else if k < 16 then 9790
  else if k < 20 then 9870
  else if k < 512 then 9890
  else 10000

/-- Number of served windows out of `10000` at budget `k`, mathematical text,
ctx 1024. -/
def mathT1024 (k : ℕ) : ℕ :=
  if k < 8 then 0
  else if k < 12 then 9520
  else if k < 16 then 9650
  else if k < 20 then 9780
  else if k < 1024 then 9830
  else 10000











/-! ## The measured workloads -/

/-- Mathematical text at ctx 512: the realised workload with the measured sweep
and the measured full accuracy `0.3262`. -/
noncomputable def mathWorkload512 : Workload 10000 := ofCountProfile 10000 mathT512 3262

/-- Mathematical text at ctx 1024: measured sweep, measured accuracy `0.3418`. -/
noncomputable def mathWorkload1024 : Workload 10000 := ofCountProfile 10000 mathT1024 3418

/-- English prose at ctx 512: knee `16` (prior rounds), measured accuracy
`0.4460`. -/
noncomputable def proseWorkload512 : Workload 10000 := flat 10000 16 4460

/-- English prose at ctx 1024: knee `20` (prior rounds), measured accuracy
`0.4612`. -/
noncomputable def proseWorkload1024 : Workload 10000 := flat 10000 20 4612

/-- Source code at ctx 512: knee `12` (prior rounds). -/
noncomputable def codeWorkload512 : Workload 10000 := flat 10000 12 4460

/-! ## The knees are computed, over the whole admissible gate window -/










/-! ## The verdict -/





/-! ## The three-domain deployment table -/

/-- Deployment bases at ctx 512: `prose ↦ 16`, `code ↦ 12`, `math ↦ 16`. -/
def deployBase : Fin 3 → ℕ := ![16, 12, 16]






end Combinatorics.MathReadsAsProse


