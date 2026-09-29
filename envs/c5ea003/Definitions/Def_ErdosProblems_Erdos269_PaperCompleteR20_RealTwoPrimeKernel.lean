-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_RealTwoPrimeKernel
-- name    : ErdosProblems_Erdos269_PaperCompleteR20_RealTwoPrimeKernel
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:11:50.084792+00:00
-- url     : https://prove2.me/theorems/d6116d24-1aa3-4d03-bd6b-93dfbb447f65
-- title:
--   RealTwoPrimeKernel
-- statement:
--   Defines a two-prime running height at a real argument using integer floors of real logarithms and its reciprocal kernel at monomials p^i q^j.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperCompleteR20/RealTwoPrimeKernel.lean#L1-L77
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Two-generator separation for arbitrary real bases

The long paper allows real generators greater than one. Integer floors and
integer powers retain that literal domain, including nonintegral bases.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20

noncomputable section

def realTwoPrimeHeight (p q t : ℝ) : ℝ :=
  p ^ ⌊Real.logb p t⌋ * q ^ ⌊Real.logb q t⌋

def realTwoPrimeKernel (p q : ℝ) (i j : ℕ) : ℝ :=
  (realTwoPrimeHeight p q (p ^ i * q ^ j))⁻¹












end

end ErdosProblems.Erdos269.PaperCompleteR20


