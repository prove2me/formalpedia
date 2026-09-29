-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.iterIntForwardDiff_succ
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:52:32.652305+00:00
-- url     : https://prove2.me/submissions/afb42b26-62a7-4374-9db1-2bee272801ea

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

namespace ErdosProblems.Erdos243.PaperCompleteR20
open Filter
end ErdosProblems.Erdos243.PaperCompleteR20

open Filter
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR20 in
@[simp] theorem solution (k : ℕ) (u : ℕ → ℤ) :
    iterIntForwardDiff (k + 1) u = intForwardDiff (iterIntForwardDiff k u) := rfl
