-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_eventually_constant_of_forwardDiff_eventually_zero
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.eventually_constant_of_forwardDiff_eventually_zero
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T22:52:58.521443+00:00
-- url     : https://prove2.me/theorems/33e89485-6baf-403d-a7f6-1ab3b7308d20
-- title:
--   Lean source theorem: eventually_constant_of_forwardDiff_eventually_zero
-- statement:
--   An integer-valued sequence whose first forward difference is eventually zero is eventually constant.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateFiniteDifference.lean#L54-L69
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

theorem ErdosProblems.Erdos243.PaperCompleteR20.eventually_constant_of_forwardDiff_eventually_zero
    (u : ℕ → ℤ) (h : ∀ᶠ n in atTop, intForwardDiff u n = 0) :
    ∃ N : ℕ, ∀ n, N ≤ n → u n = u N := by sorry
