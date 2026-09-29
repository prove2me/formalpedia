-- Prove2me | solution 1 for ErdosProblems.Erdos68.channelNumerator_isolatedChannelUnit
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:24:20.344472+00:00
-- url     : https://prove2.me/submissions/944c567b-ff4b-4d89-9fda-d7bdbf637a19

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Theorems.Thm_ErdosProblems_Erdos68_isolatedChannelUnit_of_two_le
import Theorems.Thm_ErdosProblems_Erdos68_channelEvent_eq_of_dvd
import Theorems.Thm_ErdosProblems_Erdos68_channelEvent_eq_zero_of_not_dvd
import Theorems.Thm_ErdosProblems_Erdos68_channelNumerator_single
import Theorems.Thm_ErdosProblems_Erdos68_channelNumerator_smul
import Theorems.Thm_ErdosProblems_Erdos68_channelNumerator_sub
import Theorems.Thm_ErdosProblems_Erdos68_channelNumerator_zero
import Theorems.Thm_ErdosProblems_Erdos68_channelNumerator_sum
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



theorem channelNumerator_adjacentDifference
    {n d : ℕ} (_hn : 1 ≤ n) :
    channelNumerator (adjacentDifference n) d = channelEvent d n := by
  unfold adjacentDifference channelEvent
  rw [channelNumerator_sub, channelNumerator_single, channelNumerator_single]
  ring







theorem channelEvent_eq_indicator
    {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) :
    channelEvent d n =
      (if d ∣ n then ((d.factorial : ℤ) - 1) * (channelWeight n d : ℤ)
        else 0) := by
  by_cases hnd : d ∣ n
  · simp [hnd, channelEvent_eq_of_dvd hd hn hnd]
  · simp [hnd, channelEvent_eq_zero_of_not_dvd hd hnd]

/-- `V_d(T_n) = (d! - 1) W_{d,n} 1_{d | n}`. -/
theorem channelNumerator_adjacentDifference_eq
    {n d : ℕ} (hn : 2 ≤ n) (hd : 2 ≤ d) :
    channelNumerator (adjacentDifference n) d =
      (if d ∣ n then ((d.factorial : ℤ) - 1) * (channelWeight n d : ℤ)
        else 0) := by
  have hn0 : 0 < n := by omega
  rw [channelNumerator_adjacentDifference (by omega),
    channelEvent_eq_indicator hd hn0]

theorem channelWeight_self {n : ℕ} (hn : 0 < n) :
    channelWeight n n = 1 := by
  have hn1 : n / n = 1 := Nat.div_self hn
  rw [channelWeight, hn1, pow_one, Nat.div_self (Nat.factorial_pos n)]

/-! ## Support-sensitive factor of `12` -/

















/-! ## Channel moduli and `12 L_D` -/





















/-! ## Isolated channel units `U_n` -/
end ErdosProblems.Erdos68

open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
theorem solution
    {n d : ℕ} (hn : 2 ≤ n) (hd : 2 ≤ d) :
    channelNumerator (isolatedChannelUnit n) d =
      if d = n then ((n.factorial : ℤ) - 1) else 0 := by
  revert hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      have hn0 : 0 < n := by omega
      rw [isolatedChannelUnit_of_two_le hn, channelNumerator_sub,
        channelNumerator_adjacentDifference_eq hn hd, channelNumerator_sum]
      have hsummand :
          ∀ e ∈ Finset.Ico 2 n,
            channelNumerator
              (if e ∣ n then
                (channelWeight n e : ℤ) • isolatedChannelUnit e else 0) d =
              if e ∣ n ∧ e = d then
                (channelWeight n d : ℤ) * ((d.factorial : ℤ) - 1) else 0 := by
        intro e he
        have he2 : 2 ≤ e := (Finset.mem_Ico.mp he).1
        have helt : e < n := (Finset.mem_Ico.mp he).2
        by_cases hdiv : e ∣ n
        · rw [if_pos hdiv, channelNumerator_smul, ih e helt he2]
          by_cases hde : e = d
          · subst hde
            simp [hdiv]
          · rw [if_neg (Ne.symm hde)]
            simp [hde]
        · simp [hdiv, channelNumerator_zero]
      have hsum :
          ∑ e ∈ (Finset.Ico 2 n).attach,
              channelNumerator
                (if e.1 ∣ n then
                  (channelWeight n e.1 : ℤ) • isolatedChannelUnit e.1
                  else 0) d =
            if d ∣ n ∧ d < n then
              ((d.factorial : ℤ) - 1) * (channelWeight n d : ℤ)
            else 0 := by
        classical
        have := Finset.sum_attach (s := Finset.Ico 2 n)
          (f := fun e =>
            channelNumerator
              (if e ∣ n then
                (channelWeight n e : ℤ) • isolatedChannelUnit e else 0) d)
        rw [this, Finset.sum_congr rfl hsummand]
        by_cases hdn : d ∣ n ∧ d < n
        · have hdI : d ∈ Finset.Ico 2 n := by
            simp [Finset.mem_Ico, hd, hdn.2]
          rw [if_pos hdn, Finset.sum_eq_single d]
          · rw [if_pos ⟨hdn.1, rfl⟩]
            ring
          · intro e _he hne
            rw [if_neg fun h => hne h.2]
          · intro hnot
            exact (hnot hdI).elim
        · rw [if_neg hdn]
          apply Finset.sum_eq_zero
          intro e he
          by_cases hdiv : e ∣ n
          · have helt : e < n := (Finset.mem_Ico.mp he).2
            have hne : e ≠ d := fun h => hdn ⟨h ▸ hdiv, h ▸ helt⟩
            rw [if_neg fun h => hne h.2]
          · simp [hdiv]
      rw [hsum]
      by_cases hdn : d ∣ n
      · by_cases hlt : d < n
        · have hne : d ≠ n := ne_of_lt hlt
          simp [hdn, hlt, hne]
        · have hge : n ≤ d := Nat.le_of_not_gt hlt
          have heq : d = n :=
            le_antisymm (Nat.le_of_dvd hn0 hdn) hge
          subst heq
          simp [channelWeight_self hn0]
      · have hne : d ≠ n := fun h => hdn (h ▸ dvd_refl n)
        simp [hdn, hne]
