-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.channelScalar_twice_prime_dvd_factorial
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:20:50.613179+00:00
-- url     : https://prove2.me/submissions/adc8c4d1-a32b-46ed-aa3f-53884d6674b5

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentHorizon
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelScalar_twice_prime
import Theorems.Thm_ErdosProblems_Erdos68_channelWeight_mul_denominator
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
    channelScalar (2 * p) ∣ ((2 * p).factorial : ℤ) := by
  have hp1 : 1 ≤ p := le_trans (by decide) hp.two_le
  have hden : 2 ^ p * channelWeight (2 * p) 2 = (2 * p).factorial := by
    simpa using channelWeight_mul_denominator (2 * p) 2 (by decide)
  have hpow : (2 : ℤ) ^ p = 2 * 2 ^ (p - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hp1, pow_succ]
    ring
  refine ⟨-((2 : ℤ) ^ (p - 1)), ?_⟩
  rw [channelScalar_twice_prime hp]
  have hdenZ : (2 : ℤ) ^ p * (channelWeight (2 * p) 2 : ℤ) =
      ((2 * p).factorial : ℤ) := by exact_mod_cast hden
  rw [← hdenZ, hpow]
  ring
