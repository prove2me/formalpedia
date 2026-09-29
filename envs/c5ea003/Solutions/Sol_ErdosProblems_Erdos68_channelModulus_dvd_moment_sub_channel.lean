-- Prove2me | solution 1 for ErdosProblems.Erdos68.channelModulus_dvd_moment_sub_channel
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:20:52.768475+00:00
-- url     : https://prove2.me/submissions/f422324f-23e9-472d-a42c-9ca471ea336b

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Theorems.Thm_ErdosProblems_Erdos68_channelWeight_mul_denominator
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

theorem channelWeight_sub_factorial_dvd {d i : ℕ} (hd : 2 ≤ d) :
    ((d.factorial : ℤ) - 1) ∣
      (i.factorial : ℤ) - (channelWeight i d : ℤ) := by
  have hdpos : 0 < d := by omega
  have hmul := channelWeight_mul_denominator i d hdpos
  have hcast :
      (i.factorial : ℤ) =
        (d.factorial : ℤ) ^ (i / d) * (channelWeight i d : ℤ) := by
    exact_mod_cast hmul.symm
  have hpow : ∀ k : ℕ, ((d.factorial : ℤ) - 1) ∣
      (d.factorial : ℤ) ^ k - 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hsplit :
            (d.factorial : ℤ) ^ (k + 1) - 1 =
              (d.factorial : ℤ) * ((d.factorial : ℤ) ^ k - 1) +
                ((d.factorial : ℤ) - 1) := by ring
        rw [hsplit]
        exact dvd_add (dvd_mul_of_dvd_right ih _) dvd_rfl
  have hpow := hpow (i / d)
  rcases hpow with ⟨z, hz⟩
  refine ⟨(channelWeight i d : ℤ) * z, ?_⟩
  calc
    (i.factorial : ℤ) - (channelWeight i d : ℤ) =
        (channelWeight i d : ℤ) * ((d.factorial : ℤ) ^ (i / d) - 1) := by
          rw [hcast]; ring
    _ = (channelWeight i d : ℤ) * (((d.factorial : ℤ) - 1) * z) := by rw [hz]
    _ = ((d.factorial : ℤ) - 1) * ((channelWeight i d : ℤ) * z) := by ring
end ErdosProblems.Erdos68

open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
theorem solution
    (lam : ℕ →₀ ℤ) {d : ℕ} (hd : 2 ≤ d) :
    ((d.factorial : ℤ) - 1) ∣
      factorialMoment lam - channelNumerator lam d := by
  classical
  unfold factorialMoment channelNumerator Finsupp.sum
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro i _
  have hpt := channelWeight_sub_factorial_dvd (d := d) (i := i) hd
  change ((d.factorial : ℤ) - 1) ∣
    lam i * (i.factorial : ℤ) - lam i * (channelWeight i d : ℤ)
  have :
      lam i * (i.factorial : ℤ) - lam i * (channelWeight i d : ℤ) =
        lam i * ((i.factorial : ℤ) - (channelWeight i d : ℤ)) := by ring
  rw [this]
  exact dvd_mul_of_dvd_right hpt _
