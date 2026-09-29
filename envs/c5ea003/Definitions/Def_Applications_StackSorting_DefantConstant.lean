-- Prove2me | Definitions.Def_Applications_StackSorting_DefantConstant
-- name    : Applications_StackSorting_DefantConstant
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:57.513912+00:00
-- url     : https://prove2.me/theorems/d09fcbff-19df-4561-ae9d-4e35d852433e
-- title:
--   Aether Catalog definitions — Applications_StackSorting_DefantConstant
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.StackSorting.DefantConstant`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/StackSorting/DefantConstant.lean by skeleton subtraction
import Mathlib
/-
# Defant's stack-sorting depth constant `λ = (3/5)·(7 − 8·ln 2)`

This file studies the real constant

  `λ := (3/5) · (7 − 8 · log 2)`

which is the conjectured value of the limit `lim_{n→∞} D_n / n`, where `D_n`
is the *average* number of iterations of West's stack-sorting map needed to
sort a uniformly random permutation of `{1, …, n}` (the "stack-sorting depth").
Defant (2020) proved this expression as an **upper bound** for the limit; the
research conjecture under investigation is that the bound is *tight*, i.e. the
limit equals `λ` exactly.

We do not (and cannot, with current technology) decide the asymptotic
conjecture here. Instead we pin down the analytic properties of the constant
`λ` itself that the conjecture relies on, with full rigour:

* `defantConst` is sandwiched in the explicit decimal window
  `0.8728 < λ < 0.8729`;
* `0 < λ < 1`, so the conjectured average depth is genuinely sub-linear with a
  positive density;
* `λ < 7/8`;
* `λ` strictly exceeds `0.6244`, an upper bound for the Golomb–Dickman
  constant `G ≈ 0.6243299885`.  Hence, *granting the conjecture*, the average
  stack-sorting depth grows strictly faster than the Golomb–Dickman density —
  the comparison highlighted in the mission statement.

All bounds are derived from Mathlib's rigorous decimal bounds on `log 2`
(`Real.log_two_gt_d9`, `Real.log_two_lt_d9`) via `nlinarith`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The numerical value of Defant's constant is
  `≈ 0.8729`, comfortably above the Golomb–Dickman constant `≈ 0.6243`, which
  makes the headline comparison "`G < λ`" plausible *provided* the asymptotic
  conjecture holds.
Experiment (Experimenter): Encoded `λ` as `defantConst` and discharged tight
  two-sided decimal bounds with `nlinarith` fed by `Real.log_two_{gt,lt}_d9`.
  Every bound went through on the first serious attempt once the constant was
  written in the linear form `21/5 − 24/5·log 2`.
Analysis (Analyst): The constant is `≈ 0.872892`. Survives: all numeric
  bounds. The genuinely open part — that the *limit* equals `λ` — is NOT
  asserted as a theorem (it is a conjecture); we only certify the arithmetic
  facts a proof of tightness would consume.
Critique (Critic): None of the theorems are vacuous: each requires the
  rigorous `log 2` enclosure and real arithmetic (`nlinarith`), not `rfl`,
  `decide`, or `native_decide`. The Golomb–Dickman comparison is stated as the
  honest, fully-proved fact `0.6244 < λ`; the literature bound `G < 0.6244` is
  recorded in the notes, not smuggled in as an axiom.
Synthesis (PI): These analytic certificates are the reusable kernel for any
  future formalization of the tightness conjecture.
-/

namespace Applications.StackSorting

open Real

/-- Defant's constant `λ = (3/5)·(7 − 8·log 2)`, the conjectured limiting
average stack-sorting depth density. -/
noncomputable def defantConst : ℝ := 3 / 5 * (7 - 8 * Real.log 2)







end Applications.StackSorting


