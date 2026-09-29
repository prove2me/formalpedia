-- Prove2me | solution 1 for ErdosProblems.Erdos68.factorialMoment_isolatedChannelUnit
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:11:09.540982+00:00
-- url     : https://prove2.me/submissions/6f92286e-5b21-4710-a38b-c94e0bd54837

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Theorems.Thm_ErdosProblems_Erdos68_isolatedChannelUnit_of_two_le
import Theorems.Thm_ErdosProblems_Erdos68_factorialMoment_single
import Theorems.Thm_ErdosProblems_Erdos68_factorialMoment_smul
import Theorems.Thm_ErdosProblems_Erdos68_factorialMoment_sub
import Theorems.Thm_ErdosProblems_Erdos68_factorialMoment_zero
import Theorems.Thm_ErdosProblems_Erdos68_factorialMoment_sum
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring

/-!
# Divisor-coordinate channel basis for Erdős problem 68

The adjacent difference `T_n = n e_{n-1} - e_n` hits exactly the divisor
channels of index `n`.  Subtracting proper-divisor copies produces an
integral family `U_n` with a single nonzero channel.  On the manuscript
support `n ≥ 2`, the second channel forces an extra factor of `12` in the
moment, so annihilating channels through `D` yields `12 L_D ∣ M`.

No declaration here constructs a cofinal nonintegrality family or decides
rationality of the factorial-gap series.
-/

namespace ErdosProblems.Erdos68
open Finsupp

/-! ## Linearity of the Finsupp channel presentation -/





























/-! ## Adjacent differences `T_n` -/





theorem factorialMoment_adjacentDifference {n : ℕ} (hn : 1 ≤ n) :
    factorialMoment (adjacentDifference n) = 0 := by
  have hsucc : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
  have hfac : n.factorial = n * (n - 1).factorial := by
    simpa [hsucc] using Nat.factorial_succ (n - 1)
  unfold adjacentDifference
  rw [factorialMoment_sub, factorialMoment_single, factorialMoment_single]
  simp [hfac]











/-! ## Support-sensitive factor of `12` -/

















/-! ## Channel moduli and `12 L_D` -/





















/-! ## Isolated channel units `U_n` -/
end ErdosProblems.Erdos68

open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
theorem solution
    {n : ℕ} (hn : 2 ≤ n) :
    factorialMoment (isolatedChannelUnit n) = 0 := by
  revert hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      rw [isolatedChannelUnit_of_two_le hn, factorialMoment_sub,
        factorialMoment_adjacentDifference (by omega),
        factorialMoment_sum]
      simp only [zero_sub, neg_eq_zero]
      apply Finset.sum_eq_zero
      intro d _
      split_ifs with hdiv
      · have hdlt : d.1 < n := (Finset.mem_Ico.mp d.2).2
        have hd2 : 2 ≤ d.1 := (Finset.mem_Ico.mp d.2).1
        rw [factorialMoment_smul, ih d.1 hdlt hd2, mul_zero]
      · simp [factorialMoment_zero]
