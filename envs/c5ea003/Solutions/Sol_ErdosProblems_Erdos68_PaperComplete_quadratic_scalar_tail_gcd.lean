-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.quadratic_scalar_tail_gcd
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:24:19.365281+00:00
-- url     : https://prove2.me/submissions/8e076d82-e178-4e18-8ee0-6ace369a2fa8

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentHorizon
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_finiteScalarGcd_dvd_iff
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelScalar_twice_prime
import Theorems.Thm_ErdosProblems_Erdos68_channelWeight_mul_denominator
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelScalar_twice_prime_dvd_factorial
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_factorial_tail_divisor_closure
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

















lemma channelScalar_twice_prime_ne_zero {p : ℕ} (hp : p.Prime) :
    channelScalar (2 * p) ≠ 0 := by
  have hden := channelWeight_mul_denominator (2 * p) 2 (by decide)
  have hw : channelWeight (2 * p) 2 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hden
    exact (Nat.factorial_ne_zero (2 * p)) hden.symm
  rw [channelScalar_twice_prime hp]
  exact mul_ne_zero (by norm_num) (by exact_mod_cast hw)
end ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperComplete in
theorem solution {D p : ℕ}
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < 2 * p) (hpD : p ≤ D) :
    let H := D * (2 * p - 1)
    0 < finiteScalarGcd D H ∧
      IsScalarTailGcd D (finiteScalarGcd D H) ∧ H < 2 * D ^ 2 := by
  dsimp only
  let H := D * (2 * p - 1)
  have hp2 := hp.two_le
  have hanchor : 2 * p ≤ H := by
    dsimp [H]
    have hsub : 2 * p - 1 + 1 = 2 * p := by omega
    nlinarith
  have hgAnchor : ((finiteScalarGcd D H : ℕ) : ℤ) ∣ channelScalar (2 * p) :=
    (finiteScalarGcd_dvd_iff D H (finiteScalarGcd D H)).mp (dvd_refl _) _ hDp hanchor
  have hgpos : 0 < finiteScalarGcd D H := by
    by_contra h
    have hz : finiteScalarGcd D H = 0 := by omega
    rw [hz, Nat.cast_zero, zero_dvd_iff] at hgAnchor
    exact channelScalar_twice_prime_ne_zero hp hgAnchor
  have hfull : ∀ n : ℕ, D < n →
      ((finiteScalarGcd D H : ℕ) : ℤ) ∣ channelScalar n := by
    apply factorial_tail_divisor_closure (q := 2 * p) hD (le_refl _)
    · exact dvd_trans hgAnchor (channelScalar_twice_prime_dvd_factorial hp)
    · exact (finiteScalarGcd_dvd_iff D H _).mp (dvd_refl _)
  refine ⟨hgpos, ?_, ?_⟩
  · intro b
    constructor
    · intro hb n hn
      exact dvd_trans (by exact_mod_cast hb) (hfull n hn)
    · intro hb
      exact (finiteScalarGcd_dvd_iff D H b).mpr (fun n hn _ => hb n hn)
  · dsimp [H]
    have hsub : 2 * p - 1 + 1 = 2 * p := by omega
    nlinarith
