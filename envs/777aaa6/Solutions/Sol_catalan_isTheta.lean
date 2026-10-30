-- Prove2me | solution 1 for catalan_isTheta
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-27T04:34:43.911909+00:00
-- url     : https://prove2.me/submissions/a201f6ea-999f-4fee-95ba-6bdc9e41f183

import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.NumberTheory.Real.GoldenRatio
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
# General-exponent singularity scale

This is the Flajolet--Sedgewick Theorem VI.1 standard scale for general `α`:
`[z^n] (1 - z)^{-α} ~ n^{α-1} / Γ(α)`. The integer case
`Γ(k) = (k - 1)!` is in `SingularityInteger.lean`; the full transfer theorem
with Δ-domains and a little-o Darboux estimate is assembled in
`TransferGeneral.lean` (`transfer_theorem`).

The hypothesis `∀ m : ℕ, α ≠ -m` says `α ∉ {0, -1, -2, ...}`. It holds for
all non-integer real `α` and is the correct non-vacuous hypothesis.
-/

open scoped BigOperators
open Finset Polynomial Filter Asymptotics

lemma ascPochhammer_eval_eq_prod_range_complex (n : ℕ) (r : ℂ) :
    Polynomial.eval r (ascPochhammer ℂ n) = ∏ j ∈ Finset.range n, (r + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ascPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_natCast, ih, Finset.prod_range_succ]

lemma choose_eq_prod_range_complex (α : ℂ) (n : ℕ) :
    Ring.choose (α + n - 1) n = (∏ j ∈ Finset.range n, (α + j)) / (n.factorial : ℂ) := by
  have hmul := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (R := ℂ) α n
  have hfac : (n.factorial : ℂ) * Ring.choose (α + n - 1) n =
      ∏ j ∈ Finset.range n, (α + j) := by
    rw [← Ring.multichoose_eq α n]
    simpa [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval,
      ascPochhammer_eval_eq_prod_range_complex] using hmul
  have hne : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hne]
  simpa [mul_comm] using hfac

lemma GammaSeq_ne_zero_complex {α : ℂ} (hα : ∀ m : ℕ, α ≠ -m)
    {n : ℕ} (hn : n ≠ 0) : Complex.GammaSeq α n ≠ 0 := by
  have hfact : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hncast : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hnpow : (n : ℂ)^α ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl hncast
  have hαn : α + n ≠ 0 := by
    intro h
    exact hα n (eq_neg_of_add_eq_zero_left h)
  have hprod : (∏ j ∈ Finset.range n, (α + j)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj hzero
    exact hα j (eq_neg_of_add_eq_zero_left hzero)
  have hGs : Complex.GammaSeq α n =
      (n : ℂ)^α * (n.factorial : ℂ) /
        ((∏ j ∈ Finset.range n, (α + j)) * (α + n)) := by
    simp [Complex.GammaSeq, Finset.prod_range_succ]
  rw [hGs]
  exact div_ne_zero (mul_ne_zero hnpow hfact) (mul_ne_zero hprod hαn)

lemma choose_eq_cpow_div_gammaSeq_complex {α : ℂ} (hα : ∀ m : ℕ, α ≠ -m)
    {n : ℕ} (hn : n ≠ 0) :
    Ring.choose (α + n - 1) n =
      (n : ℂ)^α / ((α + n) * Complex.GammaSeq α n) := by
  have hfact : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hncast : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hnpow : (n : ℂ)^α ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl hncast
  have hαn : α + n ≠ 0 := by
    intro h
    exact hα n (eq_neg_of_add_eq_zero_left h)
  have hprod : (∏ j ∈ Finset.range n, (α + j)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj hzero
    exact hα j (eq_neg_of_add_eq_zero_left hzero)
  have hGs : Complex.GammaSeq α n =
      (n : ℂ)^α * (n.factorial : ℂ) /
        ((∏ j ∈ Finset.range n, (α + j)) * (α + n)) := by
    simp [Complex.GammaSeq, Finset.prod_range_succ]
  rw [choose_eq_prod_range_complex, hGs]
  field_simp [hfact, hprod, hαn, hnpow]

lemma choose_ratio_eq_gammaSeq_ratio_complex {α : ℂ} (hα : ∀ m : ℕ, α ≠ -m)
    {n : ℕ} (hn : n ≠ 0) :
    Ring.choose (α + n - 1) n / ((n : ℂ)^(α - 1) / Complex.Gamma α) =
      (Complex.Gamma α / Complex.GammaSeq α n) * ((n : ℂ) / (n + α)) := by
  have hncast : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hnpowα : (n : ℂ)^α ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl hncast
  have hnpowα1 : (n : ℂ)^(α - 1) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl hncast
  have hαn : α + n ≠ 0 := by
    intro h
    exact hα n (eq_neg_of_add_eq_zero_left h)
  have hnα : (n : ℂ) + α ≠ 0 := by
    simpa [add_comm] using hαn
  have hΓ : Complex.Gamma α ≠ 0 := Complex.Gamma_ne_zero hα
  have hGseq : Complex.GammaSeq α n ≠ 0 := GammaSeq_ne_zero_complex hα hn
  rw [choose_eq_cpow_div_gammaSeq_complex hα hn]
  rw [Complex.cpow_sub _ _ hncast, Complex.cpow_one]
  field_simp [hncast, hnpowα, hnpowα1, hαn, hnα, hΓ, hGseq]
  ring

lemma choose_ratio_tendsto_one_complex {α : ℂ} (hα : ∀ m : ℕ, α ≠ -m) :
    Tendsto (fun n : ℕ =>
      Ring.choose (α + n - 1) n / ((n : ℂ)^(α - 1) / Complex.Gamma α))
      atTop (nhds 1) := by
  have hΓ : Complex.Gamma α ≠ 0 := Complex.Gamma_ne_zero hα
  have h_event : (fun n : ℕ =>
      Ring.choose (α + n - 1) n / ((n : ℂ)^(α - 1) / Complex.Gamma α))
      =ᶠ[atTop]
      (fun n : ℕ => (Complex.Gamma α / Complex.GammaSeq α n) * ((n : ℂ) / (n + α))) := by
    exact (eventually_ne_atTop 0).mono fun n hn => choose_ratio_eq_gammaSeq_ratio_complex hα hn
  apply Filter.Tendsto.congr' h_event.symm
  have h₁ : Tendsto (fun n : ℕ => Complex.Gamma α / Complex.GammaSeq α n) atTop (nhds 1) := by
    simpa [div_self hΓ] using
      (tendsto_const_nhds (x := Complex.Gamma α)).div (Complex.GammaSeq_tendsto_Gamma α) hΓ
  have h₂ : Tendsto (fun n : ℕ => (n : ℂ) / (n + α)) atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop α
  simpa using h₁.mul h₂

theorem choose_standard_scale_complex {α : ℂ} (hα : ∀ m : ℕ, α ≠ -m) :
    (fun n : ℕ => Ring.choose (α + n - 1) n) ~[atTop]
      (fun n : ℕ => (n : ℂ)^(α - 1) / Complex.Gamma α) := by
  have hΓ : Complex.Gamma α ≠ 0 := Complex.Gamma_ne_zero hα
  have htarget : ∀ᶠ n : ℕ in atTop, (n : ℂ)^(α - 1) / Complex.Gamma α ≠ 0 := by
    refine (eventually_ne_atTop 0).mono ?_
    intro n hn
    have hncast : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hpow : (n : ℂ)^(α - 1) ≠ 0 := by
      rw [Complex.cpow_ne_zero_iff]
      exact Or.inl hncast
    exact div_ne_zero hpow hΓ
  rw [isEquivalent_iff_tendsto_one htarget]
  exact choose_ratio_tendsto_one_complex hα

/-!
# Central binomial coefficients from the general singularity scale

This file specializes the general `α`-scale
`[z^n] (1 - z)^{-α} ~ n^{α-1} / Γ(α)` to `α = 1/2`, obtaining the
classical central-binomial estimate
`Nat.centralBinom n ~ 4^n / sqrt (π n)`.
-/

open Filter Asymptotics
open scoped Topology BigOperators

lemma half_not_neg_nat : ∀ m : ℕ, (1 / 2 : ℂ) ≠ -m := by
  intro m hm
  have hr := congrArg Complex.re hm
  have hmnonneg : (0 : ℝ) ≤ m := by exact_mod_cast Nat.zero_le m
  norm_num at hr
  linarith

lemma half_choose_step (n : ℕ) :
    ((n + 1 : ℂ) *
        Ring.choose ((1 / 2 : ℂ) + (n + 1 : ℕ) - 1) (n + 1)) =
      (((1 / 2 : ℂ) + n) *
        Ring.choose ((1 / 2 : ℂ) + (n : ℕ) - 1) n) := by
  have h := Ring.choose_smul_choose (R := ℂ)
    (((1 / 2 : ℂ) + (n + 1 : ℕ) - 1)) (n := n + 1) (k := 1)
    (Nat.succ_le_succ (Nat.zero_le n))
  simpa [Nat.choose_one_right, nsmul_eq_mul, Ring.choose_one_right, Nat.cast_add,
    Nat.cast_one, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using h

lemma centralBinom_eq_four_pow_mul_half_choose (n : ℕ) :
    ((n.centralBinom : ℂ) =
      (4 : ℂ) ^ n * Ring.choose ((1 / 2 : ℂ) + (n : ℕ) - 1) n) := by
  induction n with
  | zero =>
      simp [Nat.centralBinom]
  | succ n ih =>
      have hn1 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      apply (mul_right_inj' hn1).mp
      calc
        (n + 1 : ℂ) * (((n + 1).centralBinom : ℂ))
            = (2 : ℂ) * (2 * n + 1) * (n.centralBinom : ℂ) := by
              exact_mod_cast Nat.succ_mul_centralBinom_succ n
        _ = (2 : ℂ) * (2 * n + 1) *
              ((4 : ℂ)^n * Ring.choose ((1 / 2 : ℂ) + (n : ℕ) - 1) n) := by
              rw [ih]
        _ = (n + 1 : ℂ) *
              ((4 : ℂ)^(n + 1) *
                Ring.choose ((1 / 2 : ℂ) + (n + 1 : ℕ) - 1) (n + 1)) := by
              rw [pow_succ]
              rw [show (n + 1 : ℂ) *
                    ((4 : ℂ)^n * 4 *
                      Ring.choose ((1 / 2 : ℂ) + (n + 1 : ℕ) - 1) (n + 1)) =
                    ((4 : ℂ)^n * 4) *
                      ((n + 1 : ℂ) *
                        Ring.choose ((1 / 2 : ℂ) + (n + 1 : ℕ) - 1) (n + 1)) by
                ring]
              rw [half_choose_step n]
              ring

private lemma half_scale_inner (n : ℕ) (hn : n ≠ 0) :
    (((n : ℂ)^((1 / 2 : ℂ) - 1)) /
          ((Real.pi : ℂ) ^ (1 / 2 : ℂ))) =
      (1 / (Real.sqrt (Real.pi * (n : ℝ)) : ℂ)) := by
  have hncast : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hnreal_nonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  have hnroot_sq : ((n : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = (n : ℂ) := by
    have hcpow : (((n : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) =
        (n : ℂ) ^ (1 / 2 : ℂ) := by
      simpa using Complex.ofReal_cpow hnreal_nonneg (1 / 2 : ℝ)
    rw [← hcpow]
    rw [← Complex.ofReal_pow]
    rw [← Real.sqrt_eq_rpow]
    rw [Real.sq_sqrt hnreal_nonneg]
    norm_num
  have hnroot_ne : (n : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl hncast
  have hpiroot_ne : (Real.pi : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hn_sqrt : (Real.sqrt (n : ℝ) : ℂ) = (n : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    simpa using Complex.ofReal_cpow hnreal_nonneg (1 / 2 : ℝ)
  have hpi_sqrt : (Real.sqrt Real.pi : ℂ) = (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    simpa using Complex.ofReal_cpow Real.pi_nonneg (1 / 2 : ℝ)
  have hsqrt_mul : (Real.sqrt (Real.pi * (n : ℝ)) : ℂ) =
      ((Real.pi : ℂ) ^ (1 / 2 : ℂ)) * ((n : ℂ) ^ (1 / 2 : ℂ)) := by
    rw [Real.sqrt_mul Real.pi_nonneg (n : ℝ)]
    rw [Complex.ofReal_mul, hpi_sqrt, hn_sqrt]
  rw [Complex.cpow_sub _ _ hncast, Complex.cpow_one, hsqrt_mul]
  field_simp [hncast, hnroot_ne, hpiroot_ne]
  exact hnroot_sq

lemma half_scale_to_sqrt_pi_n :
    (fun n : ℕ =>
      (4 : ℂ)^n *
        (((n : ℂ)^((1 / 2 : ℂ) - 1)) /
          ((Real.pi : ℂ) ^ (1 / 2 : ℂ)))) =ᶠ[atTop]
    (fun n : ℕ =>
      (4 : ℂ)^n / (Real.sqrt (Real.pi * (n : ℝ)) : ℂ)) := by
  exact (eventually_ne_atTop 0).mono fun n hn => by
    dsimp
    rw [half_scale_inner n hn]
    ring

theorem half_singularity_rescaled_isEquivalent :
    (fun n : ℕ =>
      (4 : ℂ)^n *
        Ring.choose ((1 / 2 : ℂ) + (n : ℕ) - 1) n)
      ~[atTop]
    (fun n : ℕ =>
      (4 : ℂ)^n / (Real.sqrt (Real.pi * (n : ℝ)) : ℂ)) := by
  have hscale :=
    choose_standard_scale_complex (α := (1 / 2 : ℂ)) half_not_neg_nat
  have hmul :
      (fun n : ℕ =>
        (4 : ℂ)^n * Ring.choose ((1 / 2 : ℂ) + (n : ℕ) - 1) n)
        ~[atTop]
      (fun n : ℕ =>
        (4 : ℂ)^n *
          (((n : ℂ)^((1 / 2 : ℂ) - 1)) / Complex.Gamma (1 / 2 : ℂ))) := by
    simpa only [Pi.mul_apply] using
      (Asymptotics.IsEquivalent.refl
        (l := atTop) (u := fun n : ℕ => (4 : ℂ)^n)).mul hscale
  have hmulpi :
      (fun n : ℕ =>
        (4 : ℂ)^n * Ring.choose ((1 / 2 : ℂ) + (n : ℕ) - 1) n)
        ~[atTop]
      (fun n : ℕ =>
        (4 : ℂ)^n *
          (((n : ℂ)^((1 / 2 : ℂ) - 1)) /
            ((Real.pi : ℂ) ^ (1 / 2 : ℂ)))) := by
    convert hmul using 1
    ext n
    rw [Complex.Gamma_one_half_eq]
  exact hmulpi.trans_eventuallyEq half_scale_to_sqrt_pi_n

theorem centralBinom_isEquivalent_complex_sqrt :
    (fun n : ℕ => (n.centralBinom : ℂ)) ~[atTop]
      (fun n : ℕ =>
        (4 : ℂ)^n / (Real.sqrt (Real.pi * (n : ℝ)) : ℂ)) := by
  have hbridge :
      (fun n : ℕ => (n.centralBinom : ℂ)) =ᶠ[atTop]
        (fun n : ℕ =>
          (4 : ℂ)^n *
            Ring.choose ((1 / 2 : ℂ) + (n : ℕ) - 1) n) := by
    exact Eventually.of_forall fun n =>
      centralBinom_eq_four_pow_mul_half_choose n
  exact hbridge.trans_isEquivalent half_singularity_rescaled_isEquivalent

/-!
# Catalan asymptotics

This file derives the standard asymptotic estimate for Catalan numbers from the
central binomial coefficient estimate.
-/

open Filter Asymptotics
open scoped Topology BigOperators

lemma catalan_eq_centralBinom_div_complex (n : ℕ) :
    (catalan n : ℂ) = (n.centralBinom : ℂ) / ((n : ℂ) + 1) := by
  have h : ((n : ℂ) + 1) * (catalan n : ℂ) = (n.centralBinom : ℂ) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (show (((n + 1) * catalan n : ℕ) : ℂ) = (n.centralBinom : ℂ) by
        exact_mod_cast succ_mul_catalan_eq_centralBinom n)
  have hn : (n : ℂ) + 1 ≠ 0 := by
    have hn' : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    simpa [Nat.cast_add, Nat.cast_one] using hn'
  rw [← h]
  field_simp [hn]

lemma catalan_eventuallyEq_centralBinom_div_complex :
    (fun n : ℕ => (catalan n : ℂ)) =ᶠ[atTop]
      (fun n : ℕ => (n.centralBinom : ℂ) / ((n : ℂ) + 1)) := by
  exact Eventually.of_forall catalan_eq_centralBinom_div_complex

lemma natCast_isEquivalent_succ_complex :
    (fun n : ℕ => (n : ℂ)) ~[atTop] (fun n : ℕ => (n : ℂ) + 1) := by
  apply isEquivalent_of_tendsto_one
  simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using
    (tendsto_natCast_div_add_atTop (1 : ℂ))

theorem catalan_isEquivalent_complex_sqrt_mul_nat :
    (fun n : ℕ => (catalan n : ℂ)) ~[atTop]
      (fun n : ℕ =>
        (4 : ℂ)^n / ((Real.sqrt (Real.pi * (n : ℝ)) : ℂ) * (n : ℂ))) := by
  have hdiv :
      (fun n : ℕ => (n.centralBinom : ℂ) / ((n : ℂ) + 1)) ~[atTop]
        (fun n : ℕ =>
          ((4 : ℂ)^n / (Real.sqrt (Real.pi * (n : ℝ)) : ℂ)) / (n : ℂ)) := by
    simpa only [Pi.div_apply] using
      centralBinom_isEquivalent_complex_sqrt.div natCast_isEquivalent_succ_complex.symm
  have hnorm :
      (fun n : ℕ =>
          ((4 : ℂ)^n / (Real.sqrt (Real.pi * (n : ℝ)) : ℂ)) / (n : ℂ)) =ᶠ[atTop]
        (fun n : ℕ =>
          (4 : ℂ)^n / ((Real.sqrt (Real.pi * (n : ℝ)) : ℂ) * (n : ℂ))) := by
    exact (eventually_ne_atTop 0).mono fun n _hn => by
      dsimp
      rw [div_div]
  exact catalan_eventuallyEq_centralBinom_div_complex.trans_isEquivalent
    (hdiv.trans_eventuallyEq hnorm)

lemma rpow_three_halves_mul_nat (n : ℕ) (hn : n ≠ 0) :
    (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) = (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  nth_rw 2 [← Real.rpow_one (n : ℝ)]
  rw [← Real.rpow_add hnpos]
  norm_num

lemma sqrt_pi_mul_nat_eq_sqrt_pi_mul_rpow (n : ℕ) (hn : n ≠ 0) :
    (Real.sqrt (Real.pi * (n : ℝ)) : ℂ) * (n : ℂ) =
      (((Real.sqrt Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)) : ℝ) : ℂ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hreal : Real.sqrt (Real.pi * (n : ℝ)) * (n : ℝ) =
      (Real.sqrt Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)) := by
    rw [Real.sqrt_mul Real.pi_nonneg (n : ℝ)]
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    rw [mul_assoc, rpow_three_halves_mul_nat n hn]
  exact_mod_cast hreal

lemma sqrt_mul_nat_eventuallyEq_rpow :
    (fun n : ℕ =>
        (4 : ℂ)^n / ((Real.sqrt (Real.pi * (n : ℝ)) : ℂ) * (n : ℂ))) =ᶠ[atTop]
      (fun n : ℕ =>
        (4 : ℂ)^n /
          (((Real.sqrt Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)) : ℝ) : ℂ)) := by
  exact (eventually_ne_atTop 0).mono fun n hn => by
    dsimp
    rw [sqrt_pi_mul_nat_eq_sqrt_pi_mul_rpow n hn]

theorem catalan_isEquivalent_complex_rpow :
    (fun n : ℕ => (catalan n : ℂ)) ~[atTop]
      (fun n : ℕ =>
        (4 : ℂ)^n /
          (((Real.sqrt Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)) : ℝ) : ℂ)) := by
  exact catalan_isEquivalent_complex_sqrt_mul_nat.trans_eventuallyEq
    sqrt_mul_nat_eventuallyEq_rpow

/-!
# Real-valued central-binomial and Catalan asymptotics

This file reflects the complex-valued asymptotic equivalents back to their
natural real-valued forms.
-/

open Filter Asymptotics
open scoped Topology BigOperators

lemma ofReal_isEquivalent_iff {f g : ℕ → ℝ} :
    ((fun n => (f n : ℂ)) ~[atTop] (fun n => (g n : ℂ))) ↔
      f ~[atTop] g := by
  constructor
  · intro h
    rw [Asymptotics.IsEquivalent] at h ⊢
    rw [Asymptotics.isLittleO_iff] at h ⊢
    intro c hc
    specialize h hc
    filter_upwards [h] with n hn
    simpa [Pi.sub_apply, ← Complex.ofReal_sub, Complex.norm_real] using hn
  · intro h
    rw [Asymptotics.IsEquivalent] at h ⊢
    rw [Asymptotics.isLittleO_iff] at h ⊢
    intro c hc
    specialize h hc
    filter_upwards [h] with n hn
    simpa [Pi.sub_apply, ← Complex.ofReal_sub, Complex.norm_real] using hn

theorem catalan_isEquivalent_real_rpow :
    (fun n : ℕ => (catalan n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        (4 : ℝ)^n / (Real.sqrt Real.pi * (n : ℝ)^(3 / 2 : ℝ))) := by
  rw [← ofReal_isEquivalent_iff]
  simpa [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow] using
    catalan_isEquivalent_complex_rpow

/-!
# Growth-rate corollaries of exact asymptotics

This file records API-level growth-rate consequences derived from the existing
asymptotic-equivalent headlines.
-/

open Filter Asymptotics
open scoped Topology BigOperators

open Filter Asymptotics
open scoped Topology BigOperators
theorem solution :
    (fun n : ℕ => (catalan n : ℝ)) =Θ[atTop]
      (fun n : ℕ =>
        (4 : ℝ)^n / (Real.sqrt Real.pi * (n : ℝ)^(3 / 2 : ℝ))) := by
  exact catalan_isEquivalent_real_rpow.isTheta
