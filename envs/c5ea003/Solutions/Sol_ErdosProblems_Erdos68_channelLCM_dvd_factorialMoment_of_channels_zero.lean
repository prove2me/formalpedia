-- Prove2me | solution 1 for ErdosProblems.Erdos68.channelLCM_dvd_factorialMoment_of_channels_zero
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:24:20.938048+00:00
-- url     : https://prove2.me/submissions/3493aa05-c038-4f76-9c5d-2886a22f39c9

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Theorems.Thm_ErdosProblems_Erdos68_channelModulus_dvd_moment_sub_channel
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





theorem channelModulus_dvd_factorialMoment_of_channel_zero
    (lam : ℕ →₀ ℤ) {d : ℕ} (hd : 2 ≤ d)
    (hzero : channelNumerator lam d = 0) :
    ((d.factorial : ℤ) - 1) ∣ factorialMoment lam := by
  simpa [hzero] using channelModulus_dvd_moment_sub_channel lam hd
end ErdosProblems.Erdos68

open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
theorem solution
    (D : ℕ) (lam : ℕ →₀ ℤ)
    (hzero : ∀ d ∈ Finset.Icc 2 D, channelNumerator lam d = 0) :
    (channelLCM D : ℤ) ∣ factorialMoment lam := by
  rw [Int.natCast_dvd]
  apply Finset.lcm_dvd
  intro d hdmem
  rw [← Int.natCast_dvd]
  have hd : 2 ≤ d := (Finset.mem_Icc.mp hdmem).1
  have hdiv := channelModulus_dvd_factorialMoment_of_channel_zero lam hd
    (hzero d hdmem)
  have hfac : 1 ≤ d.factorial :=
    Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero d)
  simpa [channelLCM, Nat.cast_sub hfac] using hdiv
