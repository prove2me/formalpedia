-- Prove2me | Theorems.Thm_XiQuantitativePublished_zeta_zero_between_1413_1414
-- name    : XiQuantitativePublished.zeta_zero_between_1413_1414
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T12:28:19.190731+00:00
-- url     : https://prove2.me/theorems/6f17bf2b-9b3b-46cb-9ddd-25102aba9e5b
-- title:
--   A critical-line zero of zeta between heights 14.13 and 14.14
-- statement:
--   There exists a real t strictly between 14.13 and 14.14 such that ζ(1/2+it)=0. This is an unconditional existence statement for Mathlib's Riemann zeta function. It does not assert that this zero is the first, unique, or simple, and makes no claim about RH.
-- source:
--   Adapted from teal-sea/zeta-lab, MIT license, commit a401821c9608526425f3d4cf7ff8e59bc37e1c79, hunts/hardy_first_zero and lean/ZetaLean/{HardyZ,Rigor,IntervalExp,IntervalCExp}.lean. https://github.com/teal-sea/zeta-lab. Mathlib arctangent bound backport from commit 065356127b1dc0016f66b7283ce0ce2c4055aa55 (Apache-2.0). Lean4.33.1 port and Branch integration: Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. No novelty claim.

import Mathlib

theorem XiQuantitativePublished.zeta_zero_between_1413_1414 : ∃ t ∈ Set.Ioo (1413 / 100 : ℝ) (707 / 50),
    riemannZeta (1 / 2 + t * Complex.I) = 0 := by sorry
