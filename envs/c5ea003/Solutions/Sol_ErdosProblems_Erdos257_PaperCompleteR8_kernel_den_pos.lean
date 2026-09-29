-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.kernel_den_pos
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:33:39.460988+00:00
-- url     : https://prove2.me/submissions/806cbc42-b02d-4ba1-9eed-9cc2d29315a5

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_FiniteMeans
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Actual finite dyadic observation means

Round 8 proof text against Lean 4.29.1 / Mathlib
5e932f97dd25535344f80f9dd8da3aab83df0fe6. NOT COMPILED in this return.
The average samples exactly the positive progression points (m+1)*L.
No independently chosen existential return is substituted for an average.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution {B : ℝ} (hB : 1 < B) {d : ℕ} (hd : 0 < d) :
    0 < B ^ d - 1 := by
  -- Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean: one_lt_pow₀,
  -- pow_nonneg, pow_pos and the power-order lemmas (opened at the pin).
  have hp : 1 < B ^ d := one_lt_pow₀ hB hd.ne'
  exact sub_pos.mpr hp
end
