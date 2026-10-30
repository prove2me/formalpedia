-- Prove2me | solution 1 for coeff_repeatedPole_isEquivalent
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T13:36:21.782978+00:00
-- url     : https://prove2.me/submissions/9ad70d7d-7fb2-49fc-a669-8a4a2eaf5daa

import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
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
open Filter Asymptotics
open scoped PowerSeries Topology BigOperators

noncomputable section

namespace PowerSeries

lemma coeff_rescale_invOneSubPow (a : ℂ) (k n : ℕ) :
    coeff (R := ℂ) n (rescale a (invOneSubPow ℂ (k + 1)).val) =
      a ^ n * (Nat.choose (k + n) k : ℂ) := by
  rw [coeff_rescale, invOneSubPow_val_succ_eq_mk_add_choose]
  simp

end PowerSeries
end

/-!
# Integer-exponent singularity scale

This file proves the first integer-exponent standard scale for singularity
analysis:
`[z^n] (1 - z)^{-k} ~ n^{k-1} / (k-1)!` for natural `k ≥ 1`.

The general non-integer transfer for `(1 - z)^{-α}` is proved in
`SingularityGeneral.lean` (coefficient scale) and `TransferGeneral.lean`
(full transfer theorem), using Gamma/binomial infrastructure and analytic
domain hypotheses (Δ-domains).
-/

open Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

lemma shifted_choose_isEquivalent (d : ℕ) :
    (fun n : ℕ => ((n + d).choose d : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ)^d / d.factorial) := by
  have h0 := (isEquivalent_choose d).comp_tendsto (Filter.tendsto_add_atTop_nat d)
  have haff :
      (fun n : ℕ => (((n + d : ℕ) : ℝ))) ~[atTop] (fun n : ℕ => (n : ℝ)) := by
    simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
      (IsEquivalent.add_const_of_norm_tendsto_atTop
        (IsEquivalent.refl (l := atTop) (u := fun n : ℕ => (n : ℝ))) (by
          simpa using
            tendsto_norm_atTop_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))))
  have h1 :
      (fun n : ℕ => (((n + d : ℕ) : ℝ))^d / d.factorial) ~[atTop]
        (fun n : ℕ => (n : ℝ)^d / d.factorial) := by
    simpa using
      (haff.pow d).div
        (IsEquivalent.refl (l := atTop) (u := fun _ : ℕ => (d.factorial : ℝ)))
  exact h0.trans h1

lemma ofReal_isEquivalent {f g : ℕ → ℝ} (hfg : f ~[atTop] g)
    (hg : ∀ᶠ n in atTop, g n ≠ 0) :
    (fun n => (f n : ℂ)) ~[atTop] (fun n => (g n : ℂ)) := by
  rw [isEquivalent_iff_tendsto_one hg] at hfg
  rw [isEquivalent_iff_tendsto_one]
  · have hc : Tendsto (fun n => ((f n / g n : ℝ) : ℂ)) atTop (𝓝 (1 : ℂ)) := by
      simpa using hfg.ofReal
    convert hc using 1
    ext n
    simp
  · filter_upwards [hg] with n hn
    exact_mod_cast hn

lemma coeff_invOneSubPow_isEquivalent (d : ℕ) :
    (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n (PowerSeries.invOneSubPow ℂ (d + 1)).val)
      ~[atTop]
    (fun n : ℕ => (n : ℂ)^d / (d.factorial : ℂ)) := by
  have hnonzero : ∀ᶠ n : ℕ in atTop, (n : ℝ)^d / d.factorial ≠ 0 := by
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.succ_le_iff.mp hn))
    have hfact : (d.factorial : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_ne_zero d)
    exact div_ne_zero (pow_ne_zero d hn0) hfact
  have hcomplex := ofReal_isEquivalent (shifted_choose_isEquivalent d) hnonzero
  simpa [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, Nat.add_comm,
    Complex.ofReal_div, Complex.ofReal_pow] using hcomplex

end

open Filter Asymptotics
open scoped PowerSeries Topology BigOperators

noncomputable section

namespace PowerSeries

lemma coeff_C_mul_rescale_invOneSubPow (c a₀ : ℂ) (d n : ℕ) :
    coeff (R := ℂ) n (C c * rescale a₀ (invOneSubPow ℂ (d + 1)).val) =
      c * a₀ ^ n * (Nat.choose (d + n) d : ℂ) := by
  rw [coeff_C_mul, coeff_rescale_invOneSubPow]
  ring

end PowerSeries

lemma shifted_choose_complex_isEquivalent (d : ℕ) :
    (fun n : ℕ => (Nat.choose (d + n) d : ℂ)) ~[atTop]
      (fun n : ℕ => (n : ℂ)^d / (d.factorial : ℂ)) := by
  simpa [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, Nat.add_comm]
    using coeff_invOneSubPow_isEquivalent d

lemma repeatedPole_coeff_model_isEquivalent (c a₀ : ℂ) (d : ℕ) :
    (fun n : ℕ => c * a₀ ^ n * (Nat.choose (d + n) d : ℂ)) ~[atTop]
      (fun n : ℕ => c * a₀ ^ n * ((n : ℂ)^d / (d.factorial : ℂ))) := by
  have hchoose := shifted_choose_complex_isEquivalent d
  have hsame : (fun n : ℕ => c * a₀ ^ n) ~[atTop] (fun n : ℕ => c * a₀ ^ n) :=
    IsEquivalent.refl (l := atTop) (u := fun n : ℕ => c * a₀ ^ n)
  exact hsame.mul hchoose

end

open Filter Asymptotics
open scoped PowerSeries Topology BigOperators
theorem solution (c a₀ : ℂ) (_ha₀ : a₀ ≠ 0) (_hc : c ≠ 0)
    (d : ℕ) :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n
      (PowerSeries.C c * PowerSeries.rescale a₀
        (PowerSeries.invOneSubPow ℂ (d + 1)).val))
      ~[atTop]
    (fun n : ℕ => c * a₀^n * ((n : ℂ)^d / (d.factorial : ℂ))) := by
  have hcoeff :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n
        (PowerSeries.C c * PowerSeries.rescale a₀
          (PowerSeries.invOneSubPow ℂ (d + 1)).val)) =
        (fun n : ℕ => c * a₀ ^ n * (Nat.choose (d + n) d : ℂ)) := by
    funext n
    exact PowerSeries.coeff_C_mul_rescale_invOneSubPow c a₀ d n
  rw [hcoeff]
  exact repeatedPole_coeff_model_isEquivalent c a₀ d
