-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.eventually_eq_zero_of_intCast_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:55:50.67916+00:00
-- url     : https://prove2.me/submissions/b62ee4d6-aef8-49b1-891f-ae62d0b264eb

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
theorem solution
    (u : ℕ → ℤ)
    (h : Tendsto (fun n => (u n : ℝ)) atTop (nhds 0)) :
    ∀ᶠ n in atTop, u n = 0 := by
  have hlo : ∀ᶠ n in atTop, (-1 : ℝ) < (u n : ℝ) :=
    (tendsto_order.1 h).1 (-1) (by norm_num)
  have hhi : ∀ᶠ n in atTop, (u n : ℝ) < 1 :=
    (tendsto_order.1 h).2 1 (by norm_num)
  filter_upwards [hlo, hhi] with n hnlo hnhi
  have hnlo' : (-1 : ℤ) < u n := by exact_mod_cast hnlo
  have hnhi' : u n < (1 : ℤ) := by exact_mod_cast hnhi
  omega
