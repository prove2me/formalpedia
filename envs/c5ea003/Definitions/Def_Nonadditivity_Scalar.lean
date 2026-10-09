-- Prove2me | Definitions.Def_Nonadditivity_Scalar
-- name    : Nonadditivity_Scalar
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:33:36.167138+00:00
-- url     : https://prove2.me/theorems/df0778db-0bc1-48e1-8ff1-8928c2c957b7
-- title:
--   Base-two logarithms and the single-use scalar bound
-- statement:
--   Define $\log_2 x=\log x/\log2$ and $a_K=\log_2(1+9/K)$. The positive constant $\log2$ permits conversion of inequalities from natural logarithms to bits. For every real $K>0$, the elementary logarithm inequality gives $a_K\le 9/(K\log2)$. These scalar quantities are used in the finite-channel information estimates.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/Scalar.lean#L26-L43

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/








/-!
# Scalar consequences of the nonadditivity construction

All logarithms in information quantities are base two. This module proves
the real-variable inequalities in the manuscript. The channel quantities
are explicit real arguments: their quantum interpretation and the unitary
existence assertion are not asserted by this module.
-/

noncomputable section

namespace Nonadditivity.Scalar

def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2
def aK (K : ℝ) : ℝ := log2 (1 + 9 / K)


theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)



theorem aK_le {K : ℝ} (hK : 0 < K) : aK K ≤ 9 / (K * Real.log 2) := by
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + 9 / K by positivity)
  have h' : Real.log (1 + 9 / K) ≤ 9 / K := by linarith
  calc
    aK K ≤ (9 / K) / Real.log 2 :=
      (div_le_div_of_nonneg_right h' log_two_pos.le)
    _ = 9 / (K * Real.log 2) := by ring



















end Nonadditivity.Scalar


