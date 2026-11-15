-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_riemannZeta_ofReal_le_one_add_inv_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:21:01.260296+00:00
-- url     : https://prove2.me/submissions/8486dd33-9e6a-4766-a92c-d013885429bb

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PrimeHarmonicProductBound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Field

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section






/-!
# Polylogarithmic bounds for a finite prime Euler product

This file bounds

`∏ p ∈ Nat.primesLE R, (1 + A / p)`.

The elementary comparison with the full harmonic sum gives an exponential
bound.  More importantly for Fourier-tail estimates, shifting the Euler
product of the Riemann zeta function to

`s = 1 + 1 / log R`

gives a polynomial bound in `log R`.  This avoids requiring a separately
formalized Mertens theorem.
-/

/-
The two integral-test lemmas below are backported from
Mathlib/Analysis/SumIntegralComparisons.lean at
db584cd6d46c92f209a44c0f1c829460d327499d.
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson, Alastair Irving
-/
section GreenTaoIntegralTestCompatibility

open Set MeasureTheory MeasureSpace intervalIntegral
open scoped BigOperators

variable {f : ℝ → ℝ}

lemma AntitoneOn.sum_Ico_le_integral {a b : ℕ} (anti : AntitoneOn f (Icc a b))
    (integrable : IntegrableOn f (Ioi a)) (nonneg : ∀ t ∈ Ioi (a : ℝ), 0 ≤ f t) :
    ∑ n ∈ Finset.Ico a b, f ↑(n + 1) ≤ ∫ x in Ioi (a : ℝ), f x := by
  by_cases! hab : b < a
  · simpa [Finset.Ico_eq_empty_of_le hab.le] using setIntegral_nonneg measurableSet_Ioi nonneg
  grw [anti.sum_le_integral_Ico hab, integral_of_le (mod_cast hab)]
  apply setIntegral_mono_set integrable _ (Ioc_subset_Ioi_self.eventuallyLE)
  exact ae_restrict_of_forall_mem measurableSet_Ioi nonneg

open Filter Finset in
theorem AntitoneOn.tsum_comp_add_le_integral (N : ℕ) (anti : AntitoneOn f (Ici (N : ℝ)))
    (integrable : IntegrableOn f (Ioi (N : ℝ))) (nonneg : ∀ t ∈ Ioi (N : ℝ), 0 ≤ f t) :
    ∑' (n : ℕ), f (n + N + 1 : ℕ) ≤ ∫ x in Ioi (N : ℝ), f x := by
  refine tsum_le_of_sum_le' (integral_nonneg_of_ae ?_) fun s ↦ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] using nonneg
  · obtain ⟨t, ht⟩ := tendsto_finset_range.eventually (Ici_mem_atTop s) |>.exists
    calc
      ∑ i ∈ s, f ↑(i + N + 1) ≤ ∑ i ∈ range t, f ↑(i + N + 1) :=
        sum_le_sum_of_subset_of_nonneg ht <| by grind
      _ = ∑ i ∈ Ico N (N + t), f ↑(i + 1) := by rw [Finset.sum_Ico_eq_sum_range]; grind
      _ ≤ ∫ (x : ℝ) in Set.Ioi (N : ℝ), f x :=
        (anti.mono <| by grind).sum_Ico_le_integral integrable nonneg

end GreenTaoIntegralTestCompatibility

namespace Wikipedia.SzemeredisTheorem

open Filter Set
open scoped BigOperators Topology





































end Wikipedia.SzemeredisTheorem

end
/-!
# Polylogarithmic bounds for a finite prime Euler product

This file bounds

`∏ p ∈ Nat.primesLE R, (1 + A / p)`.

The elementary comparison with the full harmonic sum gives an exponential
bound.  More importantly for Fourier-tail estimates, shifting the Euler
product of the Riemann zeta function to

`s = 1 + 1 / log R`

gives a polynomial bound in `log R`.  This avoids requiring a separately
formalized Mertens theorem.
-/
open Wikipedia.SzemeredisTheorem
open Filter Set
open scoped BigOperators Topology

open Wikipedia.SzemeredisTheorem in
/-- On the real half-line to the right of one, the zeta function has the
elementary integral-test bound `ζ(s) ≤ 1 + 1 / (s - 1)`. -/
theorem solution
    {s : ℝ} (hs : 1 < s) :
    ‖riemannZeta (s : ℂ)‖ ≤ 1 + (s - 1)⁻¹ := by
  have hsC : 1 < ((s : ℂ).re) := by simpa
  have hs0C : (s : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hs))
  have hneg : -s ≠ 0 :=
    neg_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one hs))
  have hzero : (0 : ℝ) ^ (-s) = 0 :=
    Real.zero_rpow hneg
  have hsumC :=
    summable_riemannZetaSummand (s := (s : ℂ)) hsC
  have hsumR : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) := by
    exact Real.summable_nat_rpow.mpr (by linarith)
  have hsumSucc :
      Summable (fun n : ℕ => (Nat.succ n : ℝ) ^ (-s)) :=
    hsumR.comp_injective Nat.succ_injective
  have htail :
      ∑' n : ℕ, (Nat.succ (Nat.succ n) : ℝ) ^ (-s) ≤
        ∫ x : ℝ in Set.Ioi ((1 : ℕ) : ℝ), x ^ (-s) := by
    simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
      AntitoneOn.tsum_comp_add_le_integral
      (f := fun x : ℝ => x ^ (-s)) 1
      ((Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
        (by linarith)).mono
          (by
            intro x hx
            exact (show (0 : ℝ) < x from
              lt_of_lt_of_le (by norm_num) hx)))
      (integrableOn_Ioi_rpow_of_lt
        (by linarith) (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ)))
      (fun x hx => Real.rpow_nonneg
        (le_of_lt (lt_trans (by norm_num) hx)) _)
  calc
    ‖riemannZeta (s : ℂ)‖ =
        ‖∑' n : ℕ,
          riemannZetaSummandHom
            hs0C n‖ := by
      rw [tsum_riemannZetaSummand hsC]
    _ ≤ ∑' n : ℕ,
        ‖riemannZetaSummandHom
          hs0C n‖ :=
      norm_tsum_le_tsum_norm hsumC
    _ = ∑' n : ℕ, (n : ℝ) ^ (-s) := by
      apply tsum_congr
      intro n
      rw [riemannZetaSummandHom]
      simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
      rw [← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_nonneg
          (Nat.cast_nonneg n)
          (by
            change -s ≠ 0
            exact neg_ne_zero.mpr
              (ne_of_gt (lt_trans zero_lt_one hs)))]
      simp
    _ = 1 + ∑' n : ℕ,
        (Nat.succ (Nat.succ n) : ℝ) ^ (-s) := by
      rw [hsumR.tsum_eq_zero_add]
      rw [show ((0 : ℕ) : ℝ) ^ (-s) = 0 by simpa using hzero]
      simp only [zero_add]
      change (∑' n : ℕ, (Nat.succ n : ℝ) ^ (-s)) =
        1 + ∑' n : ℕ, (Nat.succ (Nat.succ n) : ℝ) ^ (-s)
      rw [hsumSucc.tsum_eq_zero_add]
      norm_num
    _ ≤ 1 + ∫ x : ℝ in Set.Ioi ((1 : ℕ) : ℝ), x ^ (-s) :=
      by gcongr
    _ = 1 + (s - 1)⁻¹ := by
      rw [integral_Ioi_rpow_of_lt
        (a := -s) (c := ((1 : ℕ) : ℝ))
        (by linarith) (by norm_num)]
      norm_num [Real.one_rpow]
      have hden : -s + 1 = -(s - 1) := by ring
      rw [hden]
      simp only [neg_div_neg_eq, one_div]
