-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.channelScalar_twice_prime
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:16:37.295825+00:00
-- url     : https://prove2.me/submissions/29081f92-6647-45f9-8c12-e43ad30bbe46

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentHorizon
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelScalar_odd
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelScalar_recurrence
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelScalar_two
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_divisor_twice_prime
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
theorem solution {p : ℕ} (hp : p.Prime) :
    channelScalar (2 * p) = -2 * (channelWeight (2 * p) 2 : ℤ) := by
  classical
  have hp2 : 2 ≤ p := hp.two_le
  rw [channelScalar_recurrence (by omega)]
  have h2mem : 2 ∈ Finset.Ico 2 (2 * p) := by
    simp only [Finset.mem_Ico]; omega
  rw [Finset.sum_eq_single 2]
  · simp [channelScalar_two]
    ring
  · intro d hd hne
    by_cases hdn : d ∣ 2 * p
    · have hd2 : 2 ≤ d := (Finset.mem_Ico.mp hd).1
      have hdlt : d < 2 * p := (Finset.mem_Ico.mp hd).2
      rcases divisor_twice_prime hp hd2 hdlt hdn with h | h
      · exact (hne h).elim
      · subst d
        have hpne : p ≠ 2 := hne
        have hodd : Odd p := hp.odd_of_ne_two hpne
        simp [hdn, channelScalar_odd hp2 hodd]
    · simp [hdn]
  · exact fun h => (h h2mem).elim
