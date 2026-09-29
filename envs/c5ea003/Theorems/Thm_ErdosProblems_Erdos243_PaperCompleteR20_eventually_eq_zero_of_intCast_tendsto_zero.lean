-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_eventually_eq_zero_of_intCast_tendsto_zero
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.eventually_eq_zero_of_intCast_tendsto_zero
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T22:54:29.02982+00:00
-- url     : https://prove2.me/theorems/a94fd3eb-5672-4e16-a7e7-e39b0b6d091b
-- title:
--   Lean source theorem: eventually_eq_zero_of_intCast_tendsto_zero
-- statement:
--   If the real casts of an integer-valued sequence tend to zero, the integer values are eventually exactly zero.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateFiniteDifference.lean#L32-L44
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

theorem ErdosProblems.Erdos243.PaperCompleteR20.eventually_eq_zero_of_intCast_tendsto_zero
    (u : ℕ → ℤ)
    (h : Tendsto (fun n => (u n : ℝ)) atTop (nhds 0)) :
    ∀ᶠ n in atTop, u n = 0 := by sorry
