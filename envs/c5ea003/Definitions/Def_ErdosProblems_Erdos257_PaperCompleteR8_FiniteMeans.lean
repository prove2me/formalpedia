-- Prove2me | Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_FiniteMeans
-- name    : ErdosProblems_Erdos257_PaperCompleteR8_FiniteMeans
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T18:44:23.469862+00:00
-- url     : https://prove2.me/theorems/141685e8-e44e-43c5-a7eb-eaff10484dc5
-- title:
--   Kernel weights and finite progression and dyadic means
-- statement:
--   This bundle defines the kernel weight B^(n mod d)/(B^d−1), a finite mean over T positive multiples of L, and a mean of those progression means over M consecutive dyadic sample sizes starting at R.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/FiniteMeans.lean#L1-L166
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
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

/-- The literal modular atom requested in mandate 1a. -/
def kernelWeight (B : ℝ) (d n : ℕ) : ℝ :=
  B ^ (n % d) / (B ^ d - 1)

/-- Average at the T positive multiples of L. -/
def progressionMean (L T : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ m ∈ Finset.range T, f ((m + 1) * L)) / (T : ℝ)

/-- Average the progression averages over R ≤ j < R+M, T=2^j. -/
def dyadicMean (L R M : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ j ∈ Finset.Ico R (R + M), progressionMean L (2 ^ j) f) / (M : ℝ)

























end ErdosProblems.Erdos257.PaperCompleteR8
end


