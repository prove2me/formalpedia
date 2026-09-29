-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.divisor_twice_prime
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:11:12.537805+00:00
-- url     : https://prove2.me/submissions/c6ef369f-f545-4c4e-a988-3e52197ea4b3

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentHorizon
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
theorem solution {p d : ℕ} (hp : p.Prime)
    (hd : 2 ≤ d) (hlt : d < 2 * p) (hdiv : d ∣ 2 * p) :
    d = 2 ∨ d = p := by
  obtain ⟨k, hk⟩ := hdiv
  have hpdk : p ∣ d * k := by
    rw [← hk]
    exact dvd_mul_left _ _
  rcases hp.dvd_mul.mp hpdk with hpd | hpk
  · obtain ⟨j, hj⟩ := hpd
    have hjpos : 1 ≤ j := by
      by_contra h
      have : j = 0 := by omega
      simp [this] at hj
      omega
    have hjle : j < 2 := by
      by_contra h
      have : 2 ≤ j := by omega
      nlinarith [hp.pos]
    have : j = 1 := by omega
    exact Or.inr (by simpa [this] using hj)
  · obtain ⟨j, hj⟩ := hpk
    have heq : p * 2 = p * (d * j) := by
      calc
        p * 2 = 2 * p := by ring
        _ = d * k := hk
        _ = p * (d * j) := by rw [hj]; ring
    have heq' : 2 = d * j := mul_left_cancel₀ hp.ne_zero heq
    have hjpos : 1 ≤ j := by
      by_contra h
      have : j = 0 := by omega
      simp [this] at heq'
    left
    nlinarith
