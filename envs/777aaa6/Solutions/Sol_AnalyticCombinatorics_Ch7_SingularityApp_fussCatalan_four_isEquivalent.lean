-- Prove2me | solution 1 for AnalyticCombinatorics.Ch7.SingularityApp.fussCatalan_four_isEquivalent
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T19:10:23.752186+00:00
-- url     : https://prove2.me/submissions/527f3573-c999-4e84-b123-62a26a18c2c1

import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TernaryTrees
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_FussCatalan
import Mathlib
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ternary trees and the Fuss-Catalan asymptotic

The number of full ternary trees with `n` internal nodes is
`1 / (2n + 1) * binom(3n,n)`.  This file proves the corresponding
Fuss-Catalan asymptotic directly from Stirling's formula.
-/

open Filter Asymptotics
open scoped Topology

lemma rpow_three_halves_mul_nat_real (n : ℕ) (hn : n ≠ 0) :
    (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) = (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  nth_rw 2 [← Real.rpow_one (n : ℝ)]
  rw [← Real.rpow_add hnpos]
  norm_num

/-!
# General Fuss-Catalan asymptotic

For fixed `p ≥ 2`, this file derives the Fuss-Catalan asymptotic
from Stirling's formula:

`1 / ((p - 1)n + 1) * choose (pn) n`
is equivalent to
`C_p * r_p^n * n^(-3/2)`, with
`r_p = p^p / (p - 1)^(p - 1)` and
`C_p = sqrt p / ((p - 1)^(3/2) sqrt (2π))`.
-/

open Filter Asymptotics
open scoped Topology

lemma fussCatalan_succ_choose_dvd (q n : ℕ) :
    q * n + 1 ∣ Nat.choose ((q + 1) * n) n := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hrel := Nat.choose_succ_right_eq ((q + 1) * n) (n - 1)
    have hpred : n - 1 + 1 = n := Nat.sub_one_add_one hn
    have hsub : (q + 1) * n - (n - 1) = q * n + 1 := by
      rw [Nat.succ_mul]
      omega
    rw [hpred, hsub] at hrel
    have hdvd : q * n + 1 ∣ Nat.choose ((q + 1) * n) n * n := by
      rw [hrel, mul_comm]
      exact dvd_mul_left _ _
    have hcop : Nat.Coprime (q * n + 1) n := by
      have h : q * n + 1 = n * q + 1 := by
        rw [Nat.mul_comm q n]
      rw [h]
      exact (Nat.coprime_mul_left_add_left 1 n q).2 (by simp)
    exact hcop.dvd_of_dvd_mul_left (by simpa [mul_comm] using hdvd)

theorem fussCatalan_choose_dvd (p n : ℕ) (hp : 2 ≤ p) :
    (p - 1) * n + 1 ∣ Nat.choose (p * n) n := by
  have hq : 1 ≤ p - 1 := by omega
  have hpq : p - 1 + 1 = p := by omega
  simpa [hpq] using fussCatalan_succ_choose_dvd (p - 1) n

lemma fussCatalan_cast (p n : ℕ) (hp : 2 ≤ p) :
    (fussCatalan p n : ℝ) =
      ((Nat.choose (p * n) n : ℕ) : ℝ) / ((((p - 1) * n + 1 : ℕ) : ℝ)) := by
  unfold fussCatalan
  exact Nat.cast_div (fussCatalan_choose_dvd p n hp) (by positivity)

lemma choose_succ_mul_cast (q n : ℕ) :
    ((Nat.choose ((q + 1) * n) n : ℕ) : ℝ) =
      (((((q + 1) * n).factorial : ℕ) : ℝ) /
        ((((n.factorial : ℕ) : ℝ) * ((((q * n).factorial : ℕ) : ℝ))))) := by
  have hle : n ≤ (q + 1) * n := by
    rw [Nat.succ_mul]
    omega
  rw [Nat.cast_choose ℝ hle]
  have hsub : (q + 1) * n - n = q * n := by
    rw [Nat.succ_mul]
    omega
  rw [hsub]

lemma tendsto_const_mul_atTop (a : ℕ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => a * n) atTop atTop := by
  simpa [nsmul_eq_mul] using
    ((tendsto_id : Tendsto (fun n : ℕ => n) atTop atTop).nsmul_atTop ha)

lemma factorial_const_mul_isEquivalent (a : ℕ) (ha : 0 < a) :
    (fun n : ℕ => (((a * n).factorial : ℕ) : ℝ)) ~[atTop]
      (fun n : ℕ => stirlingScale (a * n)) := by
  change (((fun m : ℕ => ((m.factorial : ℕ) : ℝ)) ∘ (fun n : ℕ => a * n)) ~[atTop]
    ((fun m : ℕ => stirlingScale m) ∘ (fun n : ℕ => a * n)))
  unfold stirlingScale
  exact Stirling.factorial_isEquivalent_stirling.comp_tendsto (tendsto_const_mul_atTop a ha)

lemma factorial_ratio_succ_isEquivalent (q : ℕ) (hq : 1 ≤ q) :
    (fun n : ℕ => ((((q + 1) * n).factorial : ℕ) : ℝ) /
      ((((n.factorial : ℕ) : ℝ) * ((((q * n).factorial : ℕ) : ℝ))))) ~[atTop]
    (fun n : ℕ => stirlingScale ((q + 1) * n) /
      (stirlingScale n * stirlingScale (q * n))) := by
  have hden := Stirling.factorial_isEquivalent_stirling.mul
    (factorial_const_mul_isEquivalent q (by omega))
  simpa only [Pi.div_apply, Pi.mul_apply] using
    (factorial_const_mul_isEquivalent (q + 1) (Nat.succ_pos q)).div hden

lemma power_ratio_core_succ (n q : ℕ) (y : ℝ) (hy : y ≠ 0) (hq : (q : ℝ) ≠ 0) :
    ((((q + 1 : ℕ) : ℝ) * y) ^ ((q + 1) * n)) /
      (y ^ n * (((q : ℝ) * y) ^ (q * n))) =
      ((((q + 1 : ℕ) : ℝ) ^ (q + 1)) / ((q : ℝ) ^ q)) ^ n := by
  rw [pow_mul (((q + 1 : ℕ) : ℝ) * y) (q + 1) n,
    pow_mul ((q : ℝ) * y) q n]
  rw [mul_pow, mul_pow, div_pow]
  field_simp [pow_ne_zero n hy, pow_ne_zero (q * n) hy, pow_ne_zero q hq,
    pow_ne_zero n (pow_ne_zero q hq), pow_ne_zero (q * n) hq]
  rw [pow_succ, mul_pow]
  ring_nf

lemma stirling_power_ratio_succ (q n : ℕ) (hq : 1 ≤ q) (hn : n ≠ 0) :
    ((((((q + 1) * n : ℕ) : ℝ) / Real.exp 1) ^ ((q + 1) * n)) /
      ((((n : ℝ) / Real.exp 1) ^ n) *
        (((((q * n : ℕ) : ℝ) / Real.exp 1)) ^ (q * n)))) =
      fussCatalanBase (q + 1) ^ n := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hE : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  have hy : (n : ℝ) / Real.exp 1 ≠ 0 := div_ne_zero hnR hE
  have hqR : (q : ℝ) ≠ 0 := by positivity
  rw [show ((((q + 1) * n : ℕ) : ℝ) / Real.exp 1) =
      (((q + 1 : ℕ) : ℝ)) * ((n : ℝ) / Real.exp 1) by
        norm_num [Nat.cast_mul]
        ring,
    show ((((q * n : ℕ) : ℝ) / Real.exp 1)) =
      (q : ℝ) * ((n : ℝ) / Real.exp 1) by
        norm_num [Nat.cast_mul]
        ring]
  rw [power_ratio_core_succ n q ((n : ℝ) / Real.exp 1) hy hqR]
  simp [fussCatalanBase]

lemma stirling_sqrt_ratio_succ (q n : ℕ) (hq : 1 ≤ q) (hn : n ≠ 0) :
    Real.sqrt (2 * (((q + 1) * n : ℕ) : ℝ) * Real.pi) /
      (Real.sqrt (2 * (n : ℝ) * Real.pi) *
        Real.sqrt (2 * ((q * n : ℕ) : ℝ) * Real.pi)) =
    Real.sqrt (((q + 1 : ℕ) : ℝ)) /
      (Real.sqrt ((q : ℝ)) * Real.sqrt (2 * Real.pi * (n : ℝ))) := by
  have hnum : Real.sqrt (2 * (((q + 1) * n : ℕ) : ℝ) * Real.pi) =
      Real.sqrt (((q + 1 : ℕ) : ℝ)) * Real.sqrt (2 * (n : ℝ) * Real.pi) := by
    rw [show 2 * (((q + 1) * n : ℕ) : ℝ) * Real.pi =
        (((q + 1 : ℕ) : ℝ)) * (2 * (n : ℝ) * Real.pi) by
          norm_num [Nat.cast_mul]
          ring]
    rw [Real.sqrt_mul (by positivity : 0 ≤ (((q + 1 : ℕ) : ℝ)))]
  have hden2 : Real.sqrt (2 * ((q * n : ℕ) : ℝ) * Real.pi) =
      Real.sqrt ((q : ℝ)) * Real.sqrt (2 * (n : ℝ) * Real.pi) := by
    rw [show 2 * ((q * n : ℕ) : ℝ) * Real.pi =
        (q : ℝ) * (2 * (n : ℝ) * Real.pi) by
          norm_num [Nat.cast_mul]
          ring]
    rw [Real.sqrt_mul (by positivity : 0 ≤ (q : ℝ))]
  have hA_ne : Real.sqrt (2 * (n : ℝ) * Real.pi) ≠ 0 := by positivity
  have hq_ne : Real.sqrt (q : ℝ) ≠ 0 := by positivity
  rw [hnum, hden2]
  rw [show 2 * (n : ℝ) * Real.pi = 2 * Real.pi * (n : ℝ) by ring]
  field_simp [hA_ne, hq_ne]

lemma stirling_choose_scale_succ_eq (q n : ℕ) (hq : 1 ≤ q) (hn : n ≠ 0) :
    stirlingScale ((q + 1) * n) / (stirlingScale n * stirlingScale (q * n)) =
      fussCatalanChooseScale (q + 1) n := by
  unfold stirlingScale fussCatalanChooseScale
  rw [show
      (Real.sqrt (2 * ↑((q + 1) * n) * Real.pi) *
            (↑((q + 1) * n) / Real.exp 1) ^ ((q + 1) * n)) /
          ((Real.sqrt (2 * ↑n * Real.pi) * (↑n / Real.exp 1) ^ n) *
            (Real.sqrt (2 * ↑(q * n) * Real.pi) *
              (↑(q * n) / Real.exp 1) ^ (q * n))) =
        (Real.sqrt (2 * ↑((q + 1) * n) * Real.pi) /
          (Real.sqrt (2 * ↑n * Real.pi) * Real.sqrt (2 * ↑(q * n) * Real.pi))) *
        (((↑((q + 1) * n) / Real.exp 1) ^ ((q + 1) * n)) /
          (((↑n / Real.exp 1) ^ n) * ((↑(q * n) / Real.exp 1) ^ (q * n)))) by
        ring_nf]
  rw [stirling_sqrt_ratio_succ q n hq hn, stirling_power_ratio_succ q n hq hn]
  simp only [Nat.add_sub_cancel]
  ring_nf

theorem choose_succ_mul_isEquivalent (q : ℕ) (hq : 1 ≤ q) :
    (fun n : ℕ => ((Nat.choose ((q + 1) * n) n : ℕ) : ℝ)) ~[atTop]
      (fun n : ℕ => fussCatalanChooseScale (q + 1) n) := by
  have hbridge :
      (fun n : ℕ => ((Nat.choose ((q + 1) * n) n : ℕ) : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => ((((q + 1) * n).factorial : ℕ) : ℝ) /
          ((((n.factorial : ℕ) : ℝ) * ((((q * n).factorial : ℕ) : ℝ))))) :=
    Eventually.of_forall (choose_succ_mul_cast q)
  have hraw := hbridge.trans_isEquivalent (factorial_ratio_succ_isEquivalent q hq)
  exact hraw.trans_eventuallyEq ((eventually_ne_atTop 0).mono fun n hn => by
    dsimp
    rw [stirling_choose_scale_succ_eq q n hq hn])

lemma natCast_isEquivalent_add_inv_real (q : ℕ) :
    (fun n : ℕ => (n : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) + (1 / (q : ℝ) : ℝ)) := by
  apply isEquivalent_of_tendsto_one
  simpa [add_comm] using tendsto_natCast_div_add_atTop (1 / (q : ℝ) : ℝ)

lemma q_mul_add_one_isEquivalent_q_mul (q : ℕ) (hq : 1 ≤ q) :
    (fun n : ℕ => (((q * n + 1 : ℕ) : ℝ))) ~[atTop]
      (fun n : ℕ => (q : ℝ) * (n : ℝ)) := by
  have hqR : (q : ℝ) ≠ 0 := by positivity
  have hmul :
      (fun n : ℕ => (q : ℝ) * (n : ℝ)) ~[atTop]
        (fun n : ℕ => (q : ℝ) * ((n : ℝ) + (1 / (q : ℝ) : ℝ))) := by
    simpa only [Pi.mul_apply] using
      (Asymptotics.IsEquivalent.refl (l := atTop) (u := fun _ : ℕ => (q : ℝ))).mul
        (natCast_isEquivalent_add_inv_real q)
  simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_one, mul_add, hqR] using hmul.symm

lemma sqrt_two_pi_mul_nat_eq_sqrt_two_pi_mul_rpow_real (n : ℕ) (hn : n ≠ 0) :
    Real.sqrt (2 * Real.pi * (n : ℝ)) * (n : ℝ) =
      Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)) := by
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [mul_assoc, rpow_three_halves_mul_nat_real n hn]

lemma sqrt_nat_mul_nat_eq_rpow_three_halves (q : ℕ) (hq : q ≠ 0) :
    Real.sqrt (q : ℝ) * (q : ℝ) = (q : ℝ) ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  exact rpow_three_halves_mul_nat_real q hq

lemma fussCatalan_scale_succ_simplified (q n : ℕ) (hq : 1 ≤ q) (hn : n ≠ 0) :
    fussCatalanChooseScale (q + 1) n / ((q : ℝ) * (n : ℝ)) =
      fussCatalanConst (q + 1) * fussCatalanBase (q + 1) ^ n *
        ((n : ℝ) ^ (-(3 / 2) : ℝ)) := by
  unfold fussCatalanChooseScale fussCatalanConst
  simp only [Nat.add_sub_cancel]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hqne : q ≠ 0 := by omega
  have hn32_ne : (n : ℝ) ^ (3 / 2 : ℝ) ≠ 0 := by positivity
  have hq32_ne : (q : ℝ) ^ (3 / 2 : ℝ) ≠ 0 := by positivity
  have hsqrt2pi_ne : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  rw [div_div]
  rw [show Real.sqrt (q : ℝ) * Real.sqrt (2 * Real.pi * (n : ℝ)) *
      ((q : ℝ) * (n : ℝ)) =
        (Real.sqrt (q : ℝ) * (q : ℝ)) *
          (Real.sqrt (2 * Real.pi * (n : ℝ)) * (n : ℝ)) by ring]
  rw [sqrt_nat_mul_nat_eq_rpow_three_halves q hqne,
    sqrt_two_pi_mul_nat_eq_sqrt_two_pi_mul_rpow_real n hn]
  rw [Real.rpow_neg hnpos.le]
  field_simp [hn32_ne, hq32_ne, hsqrt2pi_ne]

theorem fussCatalan_succ_isEquivalent_sqrt_n (q : ℕ) (hq : 1 ≤ q) :
    (fun n : ℕ => (fussCatalan (q + 1) n : ℝ)) ~[atTop]
      (fun n : ℕ => fussCatalanChooseScale (q + 1) n / ((q : ℝ) * (n : ℝ))) := by
  have hp : 2 ≤ q + 1 := by omega
  have hbridge :
      (fun n : ℕ => (fussCatalan (q + 1) n : ℝ)) =ᶠ[atTop]
        (fun n : ℕ =>
          ((Nat.choose ((q + 1) * n) n : ℕ) : ℝ) / (((q * n + 1 : ℕ) : ℝ))) :=
    Eventually.of_forall fun n => by
      simpa using fussCatalan_cast (q + 1) n hp
  have hdiv :
      (fun n : ℕ =>
          ((Nat.choose ((q + 1) * n) n : ℕ) : ℝ) / (((q * n + 1 : ℕ) : ℝ))) ~[atTop]
        (fun n : ℕ => fussCatalanChooseScale (q + 1) n / ((q : ℝ) * (n : ℝ))) := by
    simpa only [Pi.div_apply] using
      (choose_succ_mul_isEquivalent q hq).div (q_mul_add_one_isEquivalent_q_mul q hq)
  exact hbridge.trans_isEquivalent hdiv

theorem fussCatalan_succ_isEquivalent (q : ℕ) (hq : 1 ≤ q) :
    (fun n : ℕ => (fussCatalan (q + 1) n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        fussCatalanConst (q + 1) * fussCatalanBase (q + 1) ^ n *
          ((n : ℝ) ^ (-(3 / 2) : ℝ))) := by
  exact (fussCatalan_succ_isEquivalent_sqrt_n q hq).trans_eventuallyEq
    ((eventually_ne_atTop 0).mono fun n hn => by
      dsimp
      rw [fussCatalan_scale_succ_simplified q n hq hn])

/--
The general fixed-arity Fuss-Catalan asymptotic.  The statement uses the
closed forms
`r_p = p^p / (p - 1)^(p - 1)` and
`C_p = sqrt p / ((p - 1)^(3/2) sqrt (2π))`.
-/
theorem fussCatalan_isEquivalent (p : ℕ) (hp : 2 ≤ p) :
    (fun n : ℕ => (fussCatalan p n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        (Real.sqrt (p : ℝ) /
          ((((p - 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (2 * Real.pi))) *
        (((p : ℝ) ^ p / (((p - 1 : ℕ) : ℝ) ^ (p - 1))) ^ n) *
          ((n : ℝ) ^ (-(3 / 2) : ℝ))) := by
  have hq : 1 ≤ p - 1 := by omega
  have hpq : p - 1 + 1 = p := by omega
  simpa [fussCatalanConst, fussCatalanBase, hpq] using
    fussCatalan_succ_isEquivalent (p - 1) hq

/-!
# Named Fuss–Catalan instances (p-ary trees), F&S Ch VII

Concrete specializations of `fussCatalan_isEquivalent` to the classical small `p`-ary tree families:
ternary already lives in `TernaryTrees`; here we record quaternary (`p = 4`), quinary (`p = 5`) and
senary (`p = 6`), with their explicit growth bases `p^p/(p-1)^(p-1)`.

Each asymptotic is an immediate instance of the general theorem; the growth-base values are by
`norm_num`. (Opus-authored increment; no codex.)
-/

open Filter Asymptotics

open Filter Asymptotics
theorem solution :
    (fun n : ℕ => (_root_.fussCatalan 4 n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        _root_.fussCatalanConst 4 * _root_.fussCatalanBase 4 ^ n *
          ((n : ℝ) ^ (-(3 / 2) : ℝ))) := by
  simpa [_root_.fussCatalanConst, _root_.fussCatalanBase] using
    _root_.fussCatalan_isEquivalent 4 (by norm_num)
