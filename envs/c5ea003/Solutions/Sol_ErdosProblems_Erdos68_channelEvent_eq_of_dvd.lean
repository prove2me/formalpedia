-- Prove2me | solution 1 for ErdosProblems.Erdos68.channelEvent_eq_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:20:51.238091+00:00
-- url     : https://prove2.me/submissions/4aaf9181-91e0-42fd-8ae0-247544ab2fd3

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







lemma pred_div_eq_of_dvd
    {d n : ℕ} (hdpos : 0 < d) (hn : 0 < n) (hnd : d ∣ n) :
    (n - 1) / d = n / d - 1 := by
  have heq : d * (n / d) = n := Nat.mul_div_cancel' hnd
  have hq : 1 ≤ n / d :=
    Nat.succ_le_of_lt (Nat.div_pos (Nat.le_of_dvd hn hnd) hdpos)
  have hsucc : n / d - 1 + 1 = n / d := Nat.sub_add_cancel hq
  have hdecomp : n - 1 = d * (n / d - 1) + (d - 1) := by
    calc
      n - 1 = d * (n / d) - 1 := by rw [heq]
      _ = d * (n / d - 1 + 1) - 1 := by rw [hsucc]
      _ = d * (n / d - 1) + d - 1 := by rw [mul_add, mul_one]
      _ = d * (n / d - 1) + (d - 1) :=
        Nat.add_sub_assoc (Nat.succ_le_of_lt hdpos) _
  rw [hdecomp, Nat.mul_add_div hdpos]
  have : (d - 1) / d = 0 :=
    Nat.div_eq_of_lt (Nat.sub_lt hdpos (by omega))
  rw [this, Nat.add_zero]
end ErdosProblems.Erdos68

open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
theorem solution
    {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) (hnd : d ∣ n) :
    channelEvent d n =
      ((d.factorial : ℤ) - 1) * (channelWeight n d : ℤ) := by
  have hdpos : 0 < d := by omega
  have hle : d ≤ n := Nat.le_of_dvd hn hnd
  have hfloor : (n - 1) / d = n / d - 1 := pred_div_eq_of_dvd hdpos hn hnd
  have hq : n / d = (n - 1) / d + 1 := by
    have : 1 ≤ n / d := Nat.div_pos hle hdpos
    omega
  have hsucc : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
  have hfac : n.factorial = n * (n - 1).factorial := by
    simpa [hsucc] using Nat.factorial_succ (n - 1)
  have hnW := channelWeight_mul_denominator n d hdpos
  have hpredW := channelWeight_mul_denominator (n - 1) d hdpos
  have hpow :
      d.factorial ^ (n / d) =
        d.factorial ^ ((n - 1) / d) * d.factorial := by
    rw [hq, pow_succ]
  have hmul :
      d.factorial ^ ((n - 1) / d) * (d.factorial * channelWeight n d) =
        d.factorial ^ ((n - 1) / d) *
          (n * channelWeight (n - 1) d) := by
    calc
      d.factorial ^ ((n - 1) / d) * (d.factorial * channelWeight n d)
          = d.factorial ^ (n / d) * channelWeight n d := by
            rw [hpow, mul_assoc]
      _ = n.factorial := hnW
      _ = n * (n - 1).factorial := hfac
      _ = n * (d.factorial ^ ((n - 1) / d) * channelWeight (n - 1) d) := by
            rw [hpredW]
      _ = d.factorial ^ ((n - 1) / d) * (n * channelWeight (n - 1) d) := by
            ring
  have hpowpos : 0 < d.factorial ^ ((n - 1) / d) :=
    Nat.pow_pos (Nat.factorial_pos d)
  have hNW :
      d.factorial * channelWeight n d = n * channelWeight (n - 1) d :=
    Nat.eq_of_mul_eq_mul_left hpowpos hmul
  have hNWZ :
      (d.factorial : ℤ) * (channelWeight n d : ℤ) =
        (n : ℤ) * (channelWeight (n - 1) d : ℤ) := by
    exact_mod_cast hNW
  unfold channelEvent
  rw [← hNWZ]
  ring
