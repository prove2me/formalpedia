-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR16.summatory_totient_errorR16
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:26:05.560641+00:00
-- url     : https://prove2.me/submissions/6eced648-0898-48e9-927e-1449336f987b

import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Definitions.Def_ErdosProblems_Erdos1049_G02ArithmeticR16
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_summable_nonneg_dominated
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_harmonic_Icc_boundR16
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_hasSum_divisorsAntidiagonalR16
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_mu_abs_le_oneR16
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_sum_divisorsAntidiagonal_IccR16
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_zeta_two_valueR16
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_totient_constant_le_halfR16
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_totient_constant_posR16
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_totient_moebiusR16
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# G02 arithmetic suppliers: the summatory totient with an explicit error

Proves |Σ_{d≤y} φ(d) - (3/π²)y²| ≤ 2y(1 + log(1+y)) for every real y ≥ 0.
The definitions below are genuine totient/Möbius sums. No asymptotic
supplier is assumed as an axiom, typeclass field, or theorem premise.
-/

namespace ErdosProblems.Erdos1049.PaperR16
open Finset Filter Asymptotics
open scoped BigOperators Topology
set_option maxHeartbeats 2000000









lemma sum_range_succ_eq_IccR16 {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (hf : f 0 = 0) (N : ℕ) :
    (∑ d ∈ range (N + 1), f d) = ∑ d ∈ Icc 1 N, f d := by
  classical
  have hset : range (N + 1) = insert 0 (Icc 1 N) := by
    ext d
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hset, sum_insert (by simp), hf, zero_add]

lemma sum_Icc_castR16 (N : ℕ) :
    (∑ d ∈ Icc 1 N, (d : ℝ)) = (N : ℝ) * ((N : ℝ) + 1) / 2 := by
  classical
  induction N with
  | zero => simp
  | succ N ih =>
      have hset : Icc 1 (N + 1) = insert (N + 1) (Icc 1 N) := by
        ext d
        simp only [mem_Icc, mem_insert]
        omega
      rw [hset, sum_insert (by simp), ih]
      push_cast
      ring







lemma moebius_divisor_sumR16 (r : ℕ) (hr : 0 < r) :
    (∑ x ∈ r.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ)) =
      if r = 1 then 1 else 0 := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun n : ℕ => if n = 1 then (1 : ℝ) else 0)
    (g := fun _ : ℕ => (1 : ℝ))).mp
      (by
        intro n hn
        simp [Nat.one_mem_divisors, hn.ne']) r hr
  simpa using h

/-- Absolute summability is established before the Möbius series is rearranged. -/
lemma mu_series_summableR16 :
    Summable (fun d : ℕ => (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)^2) := by
  apply Summable.of_abs
  apply PaperR10.summable_nonneg_dominated (fun d => abs_nonneg _)
  · intro d
    simp only [abs_div, abs_pow, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (mu_abs_le_oneR16 d) (sq_nonneg _)
  · exact hasSum_zeta_two.summable



lemma mu_series_mul_zeta_twoR16 : muSeriesR16 * zetaTwoR16 = 1 := by
  have h := hasSum_divisorsAntidiagonalR16
    (fun d : ℕ => (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)^2)
    (fun d : ℕ => (1 : ℝ) / (d : ℝ)^2)
    (by simp) (by simp) mu_series_summableR16 hasSum_zeta_two.summable
  have he (n : ℕ) :
      (∑ x ∈ n.divisorsAntidiagonal,
        ((ArithmeticFunction.moebius x.1 : ℝ) / (x.1 : ℝ)^2) *
          (1 / (x.2 : ℝ)^2)) = if n = 1 then 1 else 0 := by
    by_cases hn : n = 0
    · subst n; simp
    · calc
        _ = (∑ x ∈ n.divisorsAntidiagonal,
            (ArithmeticFunction.moebius x.1 : ℝ)) / (n : ℝ)^2 := by
          rw [Finset.sum_div]
          apply sum_congr rfl
          intro x hx
          rw [div_mul_div_comm, mul_one, ← mul_pow, ← Nat.cast_mul,
            (Nat.mem_divisorsAntidiagonal.mp hx).1]
        _ = _ := by
          rw [moebius_divisor_sumR16 n (by omega)]
          split_ifs with h1 <;> simp [h1]
  have ht := h.tsum_eq
  simp only [he] at ht
  simpa [muSeriesR16, zetaTwoR16] using ht.symm



lemma mu_series_valueR16 : muSeriesR16 = 6 / Real.pi^2 := by
  have hp : Real.pi^2 ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have h := mu_series_mul_zeta_twoR16
  rw [zeta_two_valueR16] at h
  apply (eq_div_iff hp).mpr
  nlinarith







lemma nat_floor_divR16 (y : ℝ) (hy : 0 ≤ y) (a : ℕ) (ha : 0 < a) :
    ⌊y/(a : ℝ)⌋₊ = ⌊y⌋₊ / a := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hdiv : 0 ≤ y/(a : ℝ) := div_nonneg hy haR.le
  apply le_antisymm
  · apply (Nat.le_div_iff_mul_le ha).2
    apply (Nat.le_floor_iff hy).2
    rw [Nat.cast_mul]
    exact (le_div_iff₀ haR).1 (Nat.floor_le hdiv)
  · apply (Nat.le_floor_iff hdiv).2
    apply (le_div_iff₀ haR).2
    have ht : ((⌊y⌋₊ / a : ℕ) : ℝ)*(a : ℝ) ≤ (⌊y⌋₊ : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self ⌊y⌋₊ a
    exact ht.trans (Nat.floor_le hy)

lemma totient_moebius_prefixR16 (y : ℝ) (hy : 0 ≤ y) :
    totientPrefixR16 y =
      ∑ a ∈ Icc 1 ⌊y⌋₊, (ArithmeticFunction.moebius a : ℝ) *
        ((⌊y / (a : ℝ)⌋₊ : ℝ) * ((⌊y / (a : ℝ)⌋₊ : ℝ) + 1) / 2) := by
  unfold totientPrefixR16
  calc
    _ = ∑ r ∈ Icc 1 ⌊y⌋₊, ∑ x ∈ r.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℝ)*(x.2 : ℝ) := by
      apply sum_congr rfl
      intro r hr
      exact totient_moebiusR16 r (by have := (mem_Icc.mp hr).1; omega)
    _ = ∑ a ∈ Icc 1 ⌊y⌋₊, ∑ b ∈ Icc 1 (⌊y⌋₊/a),
        (ArithmeticFunction.moebius a : ℝ)*(b : ℝ) :=
      sum_divisorsAntidiagonal_IccR16 _
        (fun a b => (ArithmeticFunction.moebius a : ℝ) * (b : ℝ))
    _ = _ := by
      apply sum_congr rfl
      intro a ha
      rw [← mul_sum, sum_Icc_castR16,
        nat_floor_divR16 y hy a (by have := (mem_Icc.mp ha).1; omega)]

lemma triangular_floor_errorR16 (x : ℝ) (hx : 0 ≤ x) :
    |(⌊x⌋₊ : ℝ) * ((⌊x⌋₊ : ℝ) + 1) / 2 - x^2 / 2| ≤ x / 2 := by
  have hlo := Nat.floor_le hx
  have hhi := Nat.lt_floor_add_one x
  have h0 : (0 : ℝ) ≤ ⌊x⌋₊ := Nat.cast_nonneg _
  have hp := mul_nonneg (sub_nonneg.mpr hlo)
    (show 0 ≤ x + (⌊x⌋₊ : ℝ) + 1 by positivity)
  have hq := mul_nonneg (sub_nonneg.mpr hlo)
    (show 0 ≤ (⌊x⌋₊ : ℝ) + 1 - x by linarith)
  have hr := mul_nonneg h0
    (show 0 ≤ (⌊x⌋₊ : ℝ) + 1 - x by linarith)
  rw [abs_le]
  constructor <;> nlinarith

lemma inverse_square_tailR16 (m : ℕ) (hm : 1 ≤ m) :
    (∑' k : ℕ, (1 : ℝ) / ((k + (m + 1) : ℕ) : ℝ)^2) ≤ 1 / (m : ℝ) := by
  have hs : Summable (fun k : ℕ => (1 : ℝ) / ((k + (m + 1) : ℕ) : ℝ)^2) :=
    (summable_nat_add_iff (m + 1)).2 hasSum_zeta_two.summable
  apply le_of_tendsto' hs.hasSum.tendsto_sum_nat
  intro N
  have he : (∑ k ∈ range N, (1 : ℝ) / ((k + (m + 1) : ℕ) : ℝ)^2) =
      ∑ d ∈ Ioc m (m + N), ((d : ℝ)^2)⁻¹ := by
    apply sum_bij (fun k _ => k + (m + 1))
    · intro k hk; simp only [mem_Ioc]; have := mem_range.mp hk; omega
    · intro a ha b hb hab; omega
    · intro d hd
      obtain ⟨hd1, hd2⟩ := mem_Ioc.mp hd
      refine ⟨d - (m + 1), mem_range.mpr (by omega), by omega⟩
    · intro k hk; simp [one_div]
  rw [he]
  have h := sum_Ioc_inv_sq_le_sub (α := ℝ) (by omega : m ≠ 0)
    (show m ≤ m + N by omega)
  have h0 : (0 : ℝ) ≤ ((m + N : ℕ) : ℝ)⁻¹ := by positivity
  simpa only [one_div] using h.trans (sub_le_self _ h0)

lemma mu_series_prefix_tailR16 (m : ℕ) (hm : 1 ≤ m) :
    |(∑ d ∈ Icc 1 m, (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^2) -
      muSeriesR16| ≤ 1 / (m : ℝ) := by
  let f : ℕ → ℝ := fun d => (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^2
  have hs : Summable f := mu_series_summableR16
  have hd := hs.sum_add_tsum_nat_add (m + 1)
  rw [sum_range_succ_eq_IccR16 f (by simp [f]) m] at hd
  have htail : Summable (fun k => f (k + (m + 1))) :=
    (summable_nat_add_iff (m + 1)).2 hs
  have hsq : Summable (fun k : ℕ => (1 : ℝ)/((k + (m + 1) : ℕ) : ℝ)^2) :=
    (summable_nat_add_iff (m + 1)).2 hasSum_zeta_two.summable
  have hb : ∀ k, ‖f (k + (m + 1))‖ ≤
      (1 : ℝ)/((k + (m + 1) : ℕ) : ℝ)^2 := by
    intro k
    simp only [f, Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (mu_abs_le_oneR16 _) (sq_nonneg _)
  have hn := norm_tsum_le_tsum_norm htail.norm
  have hc := Summable.tsum_le_tsum hb htail.norm hsq
  have ht : |∑' k, f (k + (m + 1))| ≤ 1 / (m : ℝ) := by
    simpa only [Real.norm_eq_abs] using hn.trans (hc.trans (inverse_square_tailR16 m hm))
  have he : (∑ d ∈ Icc 1 m, f d) - muSeriesR16 =
      -(∑' k, f (k + (m + 1))) := by
    change (∑ d ∈ Icc 1 m, f d) + (∑' k, f (k + (m + 1))) = muSeriesR16 at hd
    linarith
  change |(∑ d ∈ Icc 1 m, f d) - muSeriesR16| ≤ _
  rw [he, abs_neg]
  exact ht



lemma totient_prefix_roundingR16 (y : ℝ) (hy : 0 ≤ y) :
    |totientPrefixR16 y - (y^2 / 2) *
        (∑ a ∈ Icc 1 ⌊y⌋₊, (ArithmeticFunction.moebius a : ℝ)/(a : ℝ)^2)| ≤
      (y/2) * (∑ a ∈ Icc 1 ⌊y⌋₊, (1 : ℝ)/(a : ℝ)) := by
  rw [totient_moebius_prefixR16 y hy]
  have he :
      (∑ a ∈ Icc 1 ⌊y⌋₊, (ArithmeticFunction.moebius a : ℝ) *
        ((⌊y/(a : ℝ)⌋₊ : ℝ) * ((⌊y/(a : ℝ)⌋₊ : ℝ)+1)/2)) -
      (y^2/2) * (∑ a ∈ Icc 1 ⌊y⌋₊,
        (ArithmeticFunction.moebius a : ℝ)/(a : ℝ)^2) =
      ∑ a ∈ Icc 1 ⌊y⌋₊, (ArithmeticFunction.moebius a : ℝ) *
        ((⌊y/(a : ℝ)⌋₊ : ℝ) * ((⌊y/(a : ℝ)⌋₊ : ℝ)+1)/2 -
          (y/(a : ℝ))^2/2) := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro a ha
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 from by have := (mem_Icc.mp ha).1; omega)
    field_simp [ha0]
    <;> ring
  rw [he, mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro a ha
  have ha0 : (0 : ℝ) < a := by
    exact_mod_cast (show 0 < a by have := (mem_Icc.mp ha).1; omega)
  have h := triangular_floor_errorR16 (y/(a : ℝ)) (div_nonneg hy ha0.le)
  calc
    _ = |(ArithmeticFunction.moebius a : ℝ)| *
      |(⌊y/(a : ℝ)⌋₊ : ℝ) * ((⌊y/(a : ℝ)⌋₊ : ℝ)+1)/2 -
        (y/(a : ℝ))^2/2| := abs_mul _ _
    _ ≤ 1 * ((y/(a : ℝ))/2) :=
      mul_le_mul (mu_abs_le_oneR16 a) h (abs_nonneg _) (by norm_num)
    _ = _ := by ring
end ErdosProblems.Erdos1049.PaperR16

open Finset Filter Asymptotics
open scoped BigOperators Topology
set_option maxHeartbeats 2000000
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR16 in
theorem solution (y : ℝ) (hy : 0 ≤ y) :
    |totientPrefixR16 y - totientConstantR16 * y^2| ≤ totientErrorR16 y := by
  by_cases hy1 : 1 ≤ y
  · let m : ℕ := ⌊y⌋₊
    have hm : 1 ≤ m := by
      dsimp [m]
      exact (Nat.le_floor_iff hy).2 (by simpa using hy1)
    have hml : (m : ℝ) ≤ y := Nat.floor_le hy
    have hmu : y < (m : ℝ) + 1 := Nat.lt_floor_add_one y
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hm0 : (0 : ℝ) < m := by positivity
    have hym : y / 2 ≤ (m : ℝ) := by linarith
    have hr := totient_prefix_roundingR16 y hy
    have ht := mu_series_prefix_tailR16 m hm
    have hh := harmonic_Icc_boundR16 m
    have hlog : Real.log m ≤ Real.log y := Real.log_le_log hm0 hml
    have hlog' : Real.log y ≤ Real.log (1+y) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog0 : 0 ≤ Real.log (1+y) := Real.log_nonneg (by linarith)
    have hc : (y^2 / 2) * muSeriesR16 = totientConstantR16 * y^2 := by
      rw [mu_series_valueR16]
      unfold totientConstantR16
      ring
    have hs := abs_add_le
      (totientPrefixR16 y - (y^2/2) *
        (∑ a ∈ Icc 1 m, (ArithmeticFunction.moebius a : ℝ)/(a : ℝ)^2))
      ((y^2/2) * ((∑ a ∈ Icc 1 m,
        (ArithmeticFunction.moebius a : ℝ)/(a : ℝ)^2) - muSeriesR16))
    have htail := mul_le_mul_of_nonneg_left ht (show 0 ≤ y^2/2 by positivity)
    have htail' : (y^2/2) * (1/(m : ℝ)) ≤ y := by
      have hb : (y^2/2) / (m : ℝ) ≤ y := (div_le_iff₀ hm0).2 (by nlinarith)
      simpa only [div_eq_mul_inv, one_mul] using hb
    have hround : (y/2) * (∑ a ∈ Icc 1 m, (1 : ℝ)/(a : ℝ)) ≤
        (y/2)*(1+Real.log y) :=
      mul_le_mul_of_nonneg_left (hh.trans (by linarith)) (by positivity)
    have habs : |(y^2/2) * ((∑ a ∈ Icc 1 m,
        (ArithmeticFunction.moebius a : ℝ)/(a : ℝ)^2) - muSeriesR16)| ≤ y := by
      rw [abs_mul, abs_of_nonneg (show 0 ≤ y^2/2 by positivity)]
      exact htail.trans (by convert htail' using 1 <;> ring)
    have hsplit : totientPrefixR16 y - totientConstantR16*y^2 =
        (totientPrefixR16 y - (y^2/2) *
          (∑ a ∈ Icc 1 m, (ArithmeticFunction.moebius a : ℝ)/(a : ℝ)^2)) +
        (y^2/2) * ((∑ a ∈ Icc 1 m,
          (ArithmeticFunction.moebius a : ℝ)/(a : ℝ)^2) - muSeriesR16) := by
      rw [← hc]
      ring
    rw [hsplit]
    apply hs.trans
    have hr' := hr.trans hround
    unfold totientErrorR16
    have hmul := mul_le_mul_of_nonneg_left hlog' hy
    nlinarith
  · have hylt : y < 1 := lt_of_not_ge hy1
    have hm : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr hylt
    have hc0 := totient_constant_posR16.le
    have hc := totient_constant_le_halfR16
    have hl : 0 ≤ Real.log (1+y) := Real.log_nonneg (by linarith)
    simp only [totientPrefixR16, hm, Icc_eq_empty_of_lt (by omega : (0:ℕ)<1),
      sum_empty, zero_sub, abs_neg, abs_of_nonneg (mul_nonneg hc0 (sq_nonneg y))]
    unfold totientErrorR16
    have hcy := mul_le_mul_of_nonneg_right hc (sq_nonneg y)
    have hyy := mul_nonneg hy (sub_nonneg.mpr hylt.le)
    have hyl := mul_nonneg hy hl
    nlinarith
