-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.isolated_unit_outside
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:11:09.014977+00:00
-- url     : https://prove2.me/submissions/b519d640-2c1e-4958-ab0b-e77e0aac4007

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Theorems.Thm_ErdosProblems_Erdos68_isolatedChannelUnit_of_le_one
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
# Full integral coordinate theorem

Short label res:divisor-channel-coordinates. The supplied library proves the
isolated moment/channel values, but does not prove spanning and uniqueness.
Here the auxiliary index 1 is represented by coordinate 0, and coordinate j>0
represents U_(j+1). Thus coordinates have type ℕ →₀ ℤ with no constrained
coordinate. The target coefficient vectors satisfy f 0 = 0, exactly the
paper's index convention n≥1 before its later restriction to n≥2.

The proof supplies spanning by triangular elimination, independence by the
moment/channel observables, and the explicit coefficient formula. This is
stronger than checking finitely many example matrices.
STATUS: compiled proof candidate. No axioms or proof placeholders.
-/

namespace ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
open Finsupp
end ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators
open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperComplete in
theorem solution (n i : ℕ) (hout : i = 0 ∨ n < i) :
    isolatedChannelUnit n i = 0 := by
  revert i
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i hout
    by_cases hn : n ≤ 1
    · rw [isolatedChannelUnit_of_le_one hn]
      rfl
    · have hn2 : 2 ≤ n := by omega
      have hni : n ≠ i := by omega
      have hpred : n - 1 ≠ i := by omega
      have hT : adjacentDifference n i = 0 := by
        simp [adjacentDifference, hni, hpred, Ne.symm hni, Ne.symm hpred]
      rw [isolatedChannelUnit_of_two_le hn2, Finsupp.sub_apply, hT,
        Finsupp.finset_sum_apply]
      have hsum : (∑ d ∈ (Finset.Ico 2 n).attach,
          (if d.1 ∣ n then (channelWeight n d.1 : ℤ) •
            isolatedChannelUnit d.1 else 0) i) = 0 := by
        apply Finset.sum_eq_zero
        intro d _
        by_cases hdvd : d.1 ∣ n
        · have hdlt : d.1 < n := (Finset.mem_Ico.mp d.2).2
          have hz := ih d.1 hdlt i (by omega : i = 0 ∨ d.1 < i)
          simp [hdvd, Finsupp.smul_apply, hz]
        · simp [hdvd]
      rw [hsum]
      simp
