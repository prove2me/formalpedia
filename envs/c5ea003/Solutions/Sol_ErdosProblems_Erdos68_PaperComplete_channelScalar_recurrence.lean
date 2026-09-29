-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.channelScalar_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:11:11.063985+00:00
-- url     : https://prove2.me/submissions/2874e776-5fb5-40e9-8365-0c68c653f207

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentHorizon
import Theorems.Thm_ErdosProblems_Erdos68_isolatedChannelUnit_of_two_le
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring

/-!
# The actual factorial specialisation of the quadratic tail-gcd theorem

Short-note label: res:finite-channel-moment-certificate.

This file does not assume a recurrence for an arbitrary sequence or assume
unordered-block divisibility. It derives the recurrence for U_n(1) from the
supplied definition and obtains the block identity from Mathlib's
Nat.uniformBell_mul_eq. The gcd of an infinite family is represented by its
universal property (all common divisors), avoiding an arbitrary choice of a
generator in Z. This is the exact gcd assertion, not a weaker bound.

STATUS: compiled proof candidate. No new axioms, no proof placeholders.
-/

namespace ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
end ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperComplete in
theorem solution {n : ℕ} (hn : 2 < n) :
    channelScalar n = -∑ d ∈ Finset.Ico 2 n,
      if d ∣ n then (channelWeight n d : ℤ) * channelScalar d else 0 := by
  classical
  have hT : adjacentDifference n 1 = 0 := by
    have hn1 : n ≠ 1 := by omega
    have hp1 : n - 1 ≠ 1 := by omega
    simp [adjacentDifference, hn1, hp1, Ne.symm hn1, Ne.symm hp1]
  unfold channelScalar
  rw [isolatedChannelUnit_of_two_le (by omega), Finsupp.sub_apply, hT,
    zero_sub, Finsupp.finset_sum_apply]
  congr 1
  rw [← Finset.sum_attach (s := Finset.Ico 2 n)
      (f := fun d => if d ∣ n then
        (channelWeight n d : ℤ) * isolatedChannelUnit d 1 else 0)]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd : (d : ℕ) ∣ n
  · simp [hd]
  · simp [hd]
