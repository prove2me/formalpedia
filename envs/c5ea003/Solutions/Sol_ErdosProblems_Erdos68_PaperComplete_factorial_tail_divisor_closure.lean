-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.factorial_tail_divisor_closure
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:13:10.186985+00:00
-- url     : https://prove2.me/submissions/caad5e5d-991b-4118-afee-1ff95e6e56a6

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentHorizon
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelScalar_recurrence
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









/-- A block quotient is an integer multiple of k!, not merely an integer. -/
lemma factorial_dvd_channelWeight_mul (d k : ℕ) (hd : 0 < d) :
    k.factorial ∣ channelWeight (d * k) d := by
  have hblock := Nat.uniformBell_mul_eq k (Nat.ne_of_gt hd)
  have heq : channelWeight (d * k) d = Nat.uniformBell k d * k.factorial := by
    unfold channelWeight
    rw [Nat.mul_div_cancel_left _ hd]
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hblock.symm
  rw [heq]
  exact dvd_mul_left _ _

lemma factorial_dvd_channelWeight_of_dvd {d n : ℕ}
    (hd : 0 < d) (hdn : d ∣ n) :
    (n / d).factorial ∣ channelWeight n d := by
  have heq : d * (n / d) = n := Nat.mul_div_cancel' hdn
  simpa only [heq] using factorial_dvd_channelWeight_mul d (n / d) hd
end ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperComplete in
theorem solution {D N q : ℕ} {g : ℤ}
    (hD : 2 ≤ D) (hN : D * (q - 1) ≤ N)
    (hq : g ∣ (q.factorial : ℤ))
    (hprefix : ∀ n : ℕ, D < n → n ≤ N → g ∣ channelScalar n) :
    ∀ n : ℕ, D < n → g ∣ channelScalar n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hnN : n ≤ N
    · exact hprefix n hn hnN
    · have hNn : N < n := by omega
      rw [channelScalar_recurrence (by omega)]
      apply dvd_neg.mpr
      apply Finset.dvd_sum
      intro d hd
      by_cases hdn : d ∣ n
      · simp only [if_pos hdn]
        have hd2 : 2 ≤ d := (Finset.mem_Ico.mp hd).1
        have hdlt : d < n := (Finset.mem_Ico.mp hd).2
        by_cases hdD : d ≤ D
        · have heq : d * (n / d) = n := Nat.mul_div_cancel' hdn
          have hqk : q ≤ n / d := by
            by_contra h
            have hk : n / d ≤ q - 1 := by omega
            have hnle : n ≤ D * (q - 1) := by
              calc n = d * (n / d) := heq.symm
                   _ ≤ D * (q - 1) := Nat.mul_le_mul hdD hk
            omega
          have hqW : q.factorial ∣ channelWeight n d :=
            dvd_trans (Nat.factorial_dvd_factorial hqk)
              (factorial_dvd_channelWeight_of_dvd (by omega) hdn)
          have hgW : g ∣ (channelWeight n d : ℤ) :=
            dvd_trans hq (by exact_mod_cast hqW)
          exact dvd_mul_of_dvd_left hgW _
        · exact dvd_mul_of_dvd_right (ih d hdlt (by omega)) _
      · simp [hdn]
