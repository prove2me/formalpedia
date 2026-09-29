-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
-- name    : ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T18:53:06.987682+00:00
-- url     : https://prove2.me/theorems/8dfba909-d007-436e-9c8b-c66530f2e033
-- title:
--   Integer forward differences
-- statement:
--   Defines the forward difference u(n + 1) − u(n) of an integer sequence and its iterates.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateFiniteDifference.lean#L1-L85
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Mathlib

/-!
# Erdős 243: integer finite differences for the cubic-rate bridge

This file isolates the discrete integrality step in the proof of the paper's
cubic-rate theorem.  Once the analytic comparison with the rising-factorial
model shows that a sufficiently high finite difference tends to zero, its
integer values force it to vanish identically on a tail.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Filter

/-- The forward difference of an integer sequence. -/
def intForwardDiff (u : ℕ → ℤ) (n : ℕ) : ℤ := u (n + 1) - u n

/-- Iterated integer forward differences. -/
def iterIntForwardDiff : ℕ → (ℕ → ℤ) → ℕ → ℤ
  | 0, u => u
  | k + 1, u => intForwardDiff (iterIntForwardDiff k u)














end ErdosProblems.Erdos243.PaperCompleteR20


