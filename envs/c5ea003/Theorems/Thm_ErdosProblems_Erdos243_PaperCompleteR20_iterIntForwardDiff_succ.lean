-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_iterIntForwardDiff_succ
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.iterIntForwardDiff_succ
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T22:51:20.068972+00:00
-- url     : https://prove2.me/theorems/092d3de3-7cb4-43c7-a0a8-95a3a03da781
-- title:
--   Successor step for iterated integer forward differences
-- statement:
--   For every natural k and integer sequence u, the (k + 1)-fold forward difference of u is the integer forward difference of its k-fold forward difference.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateFiniteDifference.lean#L29-L30
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Mathlib

/-!
# Erdős 243: integer finite differences for the cubic-rate bridge

This file isolates the discrete integrality step in the proof of the paper's
cubic-rate theorem.  Once the analytic comparison with the rising-factorial
model shows that a sufficiently high finite difference tends to zero, its
integer values force it to vanish identically on a tail.
-/

noncomputable section


open Filter

open ErdosProblems.Erdos243.PaperCompleteR20

@[simp] theorem ErdosProblems.Erdos243.PaperCompleteR20.iterIntForwardDiff_succ (k : ℕ) (u : ℕ → ℤ) :
    iterIntForwardDiff (k + 1) u = intForwardDiff (iterIntForwardDiff k u) := by sorry
