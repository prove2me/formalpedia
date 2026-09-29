-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.eventually_constant_of_forwardDiff_eventually_zero
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:53:56.993112+00:00
-- url     : https://prove2.me/submissions/c9a9daff-c114-4d53-9e04-1099940a6c81

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
    (u : ℕ → ℤ) (h : ∀ᶠ n in atTop, intForwardDiff u n = 0) :
    ∃ N : ℕ, ∀ n, N ≤ n → u n = u N := by
  obtain ⟨N, hN⟩ := (eventually_atTop.1 h)
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction d with
  | zero => simp
  | succ d ih =>
      have hz := hN (N + d) (by omega)
      simp only [intForwardDiff] at hz
      have hstep : u (N + d + 1) = u (N + d) := by omega
      rw [show N + (d + 1) = N + d + 1 by omega, hstep, ih (by omega)]
