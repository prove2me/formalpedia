-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_exists_sample_lt_of_dyadicMean_lt
-- name    : ErdosProblems.Erdos257.PaperCompleteR8.exists_sample_lt_of_dyadicMean_lt
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T22:17:56.163824+00:00
-- url     : https://prove2.me/theorems/6d5dd931-bf1a-49bd-bd54-ae4026b7ecac
-- title:
--   A dyadic mean below a threshold has a sampled witness
-- statement:
--   If the dyadic mean of f on a nonempty sampling range is below c, then one sampled multiple (m+1)L with scale index R≤j<R+M and m<2^j has f-value below c.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/FiniteMeans.lean#L110-L140
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

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
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7

open ErdosProblems.Erdos257.PaperCompleteR8

theorem ErdosProblems.Erdos257.PaperCompleteR8.exists_sample_lt_of_dyadicMean_lt
    (L R M : ℕ) (hM : 0 < M) (f : ℕ → ℝ) (c : ℝ)
    (hmean : dyadicMean L R M f < c) :
    ∃ j m : ℕ, R ≤ j ∧ j < R + M ∧ m < 2 ^ j ∧ f ((m + 1) * L) < c := by sorry
end
