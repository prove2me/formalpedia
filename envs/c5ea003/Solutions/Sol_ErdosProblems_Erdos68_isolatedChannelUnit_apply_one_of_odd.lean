-- Prove2me | solution 1 for ErdosProblems.Erdos68.isolatedChannelUnit_apply_one_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:11:10.584987+00:00
-- url     : https://prove2.me/submissions/328e9a31-4b91-4efb-8bfb-1a4aa624d5d9

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Theorems.Thm_ErdosProblems_Erdos68_isolatedChannelUnit_of_two_le
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

















/-! ## Support-sensitive factor of `12` -/

















/-! ## Channel moduli and `12 L_D` -/





















/-! ## Isolated channel units `U_n` -/
end ErdosProblems.Erdos68

open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
theorem solution
    {n : ℕ} (hn : 2 ≤ n) (hodd : Odd n) :
    isolatedChannelUnit n 1 = 0 := by
  suffices ∀ m, 2 ≤ m → Odd m → isolatedChannelUnit m 1 = 0 from
    this n hn hodd
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro hm hodd
      rw [isolatedChannelUnit_of_two_le hm]
      have hne2 : m ≠ 2 := fun h =>
        (h ▸ Nat.not_odd_iff_even.2 even_two) hodd
      have hne1 : m ≠ 1 := by omega
      have hT : adjacentDifference m 1 = 0 := by
        unfold adjacentDifference
        have hpred : m - 1 ≠ 1 := fun h => hne2 (by omega)
        simp [Finsupp.sub_apply, hpred, hne1]
      have hsum :
          (∑ d ∈ (Finset.Ico 2 m).attach,
              if d.1 ∣ m then
                (channelWeight m d.1 : ℤ) • isolatedChannelUnit d.1
              else 0) 1 = 0 := by
        rw [Finsupp.finset_sum_apply]
        apply Finset.sum_eq_zero
        intro d hd
        split_ifs with hdiv
        · have hd2 : 2 ≤ d.1 := (Finset.mem_Ico.mp d.2).1
          have hlt : d.1 < m := (Finset.mem_Ico.mp d.2).2
          have hodd' : Odd d.1 := Odd.of_dvd_nat hodd hdiv
          rw [Finsupp.smul_apply, ih d.1 hlt hd2 hodd', smul_zero]
        · simp
      rw [Finsupp.sub_apply, hT, zero_sub, neg_eq_zero]
      exact hsum
