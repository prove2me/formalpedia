-- Prove2me | solution 1 for MarkovMixing.wilson_method_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T17:21:17.244022+00:00
-- url     : https://prove2.me/submissions/f1d710d5-2e3e-4053-8cd2-92bb1eb0c33c

import Definitions.Def_mm_spectral
import Definitions.Def_mm_lower
import Theorems.Thm_MarkovMixing_convergence_theorem
import Theorems.Thm_MarkovMixing_distinguishing_statistic_of_pos_variance
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option maxHeartbeats 2000000

open scoped BigOperators
open MarkovMixing

namespace Wilson

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma pow_stochastic {P : Matrix V V ℝ} (hP : IsStochastic P) :
    ∀ t : ℕ, IsStochastic (P ^ t) := by
  intro t
  induction t with
  | zero =>
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · by_cases h : x = y <;> simp [Matrix.one_apply, h]
    · simp [Matrix.one_apply]
  | succ t ih =>
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun z _ => mul_nonneg (ih.1 x z) (hP.1 z y)
    · rw [pow_succ]
      have e : ∀ y : V, (P ^ t * P) x y = ∑ z, (P ^ t) x z * P z y :=
        fun y => Matrix.mul_apply
      rw [Finset.sum_congr rfl (fun y _ => e y), Finset.sum_comm]
      have e2 : ∀ z : V, ∑ y, (P ^ t) x z * P z y = (P ^ t) x z := by
        intro z
        rw [← Finset.mul_sum, hP.2 z, mul_one]
      rw [Finset.sum_congr rfl (fun z _ => e2 z), ih.2 x]

lemma pow_isDist {P : Matrix V V ℝ} (hP : IsStochastic P) (t : ℕ) (x : V) :
    IsDist (rowDist P t x) :=
  ⟨fun y => (pow_stochastic hP t).1 x y, (pow_stochastic hP t).2 x⟩

lemma distVar_eq {μ : V → ℝ} (hμ : IsDist μ) (f : V → ℝ) :
    distVar μ f = (∑ y, f y ^ 2 * μ y) - (distExp μ f) ^ 2 := by
  have hE : distExp μ f = ∑ y, f y * μ y := rfl
  show ∑ y, (f y - distExp μ f) ^ 2 * μ y = _
  have e : ∀ y : V, (f y - distExp μ f) ^ 2 * μ y
      = f y ^ 2 * μ y - 2 * distExp μ f * (f y * μ y) + (distExp μ f) ^ 2 * μ y :=
    fun y => by ring
  rw [Finset.sum_congr rfl (fun y _ => e y), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← hE, hμ.2, mul_one]
  ring

lemma distVar_nonneg {μ : V → ℝ} (hμ : IsDist μ) (f : V → ℝ) : 0 ≤ distVar μ f :=
  Finset.sum_nonneg fun y _ => mul_nonneg (sq_nonneg _) (hμ.1 y)

lemma mulVec_pow_eig {P : Matrix V V ℝ} {Φ : V → ℝ} {lam : ℝ}
    (heig : P.mulVec Φ = lam • Φ) : ∀ t : ℕ, (P ^ t).mulVec Φ = (lam ^ t) • Φ := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
      mul_comm (lam ^ t) lam]

lemma onestep {P : Matrix V V ℝ} (hP : IsStochastic P) {Φ : V → ℝ} {lam R : ℝ}
    (heig : P.mulVec Φ = lam • Φ) (hstep : ∀ z : V, ∑ y, P z y * (Φ y - Φ z) ^ 2 ≤ R) (z : V) :
    ∑ y, P z y * Φ y ^ 2 ≤ (2 * lam - 1) * Φ z ^ 2 + R := by
  have hmv : ∑ y, P z y * Φ y = lam * Φ z := by
    have h := congrFun heig z
    simpa [Matrix.mulVec, dotProduct] using h
  have e : ∀ y : V, P z y * (Φ y - Φ z) ^ 2
      = P z y * Φ y ^ 2 - 2 * Φ z * (P z y * Φ y) + Φ z ^ 2 * P z y := fun y => by ring
  have h1 : ∑ y, P z y * (Φ y - Φ z) ^ 2
      = (∑ y, P z y * Φ y ^ 2) - 2 * Φ z * (∑ y, P z y * Φ y) + Φ z ^ 2 * ∑ y, P z y := by
    rw [Finset.sum_congr rfl (fun y _ => e y), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hmv, hP.2 z] at h1
  have h2 := hstep z
  rw [h1] at h2
  linarith

lemma stat_second_moment {P : Matrix V V ℝ} (hP : IsStochastic P) {π : V → ℝ}
    (hπ : IsStationary P π) {Φ : V → ℝ} {lam R : ℝ}
    (heig : P.mulVec Φ = lam • Φ) (hstep : ∀ z : V, ∑ y, P z y * (Φ y - Φ z) ^ 2 ≤ R)
    (hlam : lam < 1) :
    2 * (1 - lam) * (∑ y, π y * Φ y ^ 2) ≤ R := by
  have hcol : ∀ y : V, ∑ z, π z * P z y = π y := fun y => congrFun hπ.2 y
  have h1 : ∑ y, π y * Φ y ^ 2 = ∑ z, π z * (∑ y, P z y * Φ y ^ 2) := by
    have e : ∀ y : V, π y * Φ y ^ 2 = ∑ z, π z * P z y * Φ y ^ 2 := by
      intro y
      rw [← Finset.sum_mul, hcol y]
    rw [Finset.sum_congr rfl (fun y _ => e y), Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have h2 : ∑ z, π z * (∑ y, P z y * Φ y ^ 2)
      ≤ (2 * lam - 1) * (∑ z, π z * Φ z ^ 2) + R := by
    calc ∑ z, π z * (∑ y, P z y * Φ y ^ 2)
        ≤ ∑ z, π z * ((2 * lam - 1) * Φ z ^ 2 + R) :=
          Finset.sum_le_sum fun z _ =>
            mul_le_mul_of_nonneg_left (onestep hP heig hstep z) (hπ.1.1 z)
      _ = (2 * lam - 1) * (∑ z, π z * Φ z ^ 2) + R := by
          have e2 : ∀ z : V, π z * ((2 * lam - 1) * Φ z ^ 2 + R)
              = (2 * lam - 1) * (π z * Φ z ^ 2) + R * π z := fun z => by ring
          rw [Finset.sum_congr rfl (fun z _ => e2 z), Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum, hπ.1.2, mul_one]
  rw [← h1] at h2
  linarith

lemma eig_orthogonal {P : Matrix V V ℝ} {π : V → ℝ} (hπ : IsStationary P π)
    {Φ : V → ℝ} {lam : ℝ} (heig : P.mulVec Φ = lam • Φ) (hne : lam ≠ 1) :
    ∑ y, Φ y * π y = 0 := by
  have hcol : ∀ z : V, ∑ y, π y * P y z = π z := fun z => congrFun hπ.2 z
  have h2 : ∑ y, π y * (P.mulVec Φ) y = ∑ z, π z * Φ z := by
    have e : ∀ y : V, π y * (P.mulVec Φ) y = ∑ z, (π y * P y z) * Φ z := by
      intro y
      show π y * (∑ z, P y z * Φ z) = _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [Finset.sum_congr rfl (fun y _ => e y), Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← Finset.sum_mul, hcol z]
  rw [heig] at h2
  have h3 : ∑ y, π y * (lam • Φ) y = lam * ∑ y, π y * Φ y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by simp [Pi.smul_apply]; ring
  rw [h3] at h2
  have h4 : (lam - 1) * (∑ y, π y * Φ y) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd (by linarith : lam = 1) hne
  · rw [← h]
    exact Finset.sum_congr rfl fun y _ => by ring

lemma le_distStationary (P : Matrix V V ℝ) (π : V → ℝ) (t : ℕ) (x : V) :
    tvDist (rowDist P t x) π ≤ distStationary P π t := by
  have hb : BddAbove (Set.range fun y : V => tvDist (rowDist P t y) π) :=
    Set.Finite.bddAbove (Set.finite_range _)
  exact le_ciSup hb x

lemma pow_entry_nonneg {P : Matrix V V ℝ} (hP : IsStochastic P) :
    ∀ (t : ℕ) (x y : V), 0 ≤ (P ^ t) x y := fun t x y => (pow_stochastic hP t).1 x y

lemma vecMul_pow {P : Matrix V V ℝ} {π : V → ℝ} (hπ : IsStationary P π) :
    ∀ t : ℕ, Matrix.vecMul π (P ^ t) = π := by
  intro t
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]

lemma pi_pos {P : Matrix V V ℝ} (hirr : MarkovMixing.Irreducible P) {π : V → ℝ}
    (hπ : IsStationary P π) (hP : IsStochastic P) : ∀ x, 0 < π x := by
  obtain ⟨y, hy⟩ : ∃ y, 0 < π y := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∑ x, π x ≤ 0 := Finset.sum_nonpos fun i _ => hcon i
    have := hπ.1.2
    linarith
  intro x
  obtain ⟨t, ht⟩ := hirr y x
  have hv : ∑ z, π z * (P ^ t) z x = π x := congrFun (vecMul_pow hπ t) x
  have h2 : π y * (P ^ t) y x ≤ ∑ z, π z * (P ^ t) z x := by
    refine Finset.single_le_sum (f := fun z => π z * (P ^ t) z x) ?_ (Finset.mem_univ y)
    exact fun z _ => mul_nonneg (hπ.1.1 z) (pow_entry_nonneg hP t z x)
  have := mul_pos hy ht
  linarith

end Wilson

open Wilson

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (hap : MarkovMixing.Aperiodic P)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary P π)
    (Φ : V → ℝ) (hΦ : Φ ≠ 0) (lam : ℝ) (heig : P.mulVec Φ = lam • Φ)
    (hlam1 : 1 / 2 < lam) (hlam2 : lam < 1)
    (R : ℝ) (hR : 0 < R)
    (hstep : ∀ x : V, ∑ y, P x y * (Φ y - Φ x) ^ 2 ≤ R)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (x : V) (hΦx : Φ x ≠ 0) :
    (2 * Real.log (1 / lam))⁻¹ *
        (Real.log ((1 - lam) * Φ x ^ 2 / (2 * R)) + Real.log ((1 - ε) / ε)) ≤
      (MarkovMixing.mixingTime P π ε : ℝ) := by
  classical
  have hlam0 : 0 < lam := by linarith
  have hpos := pi_pos hirr hπ hP
  have hΦxsq : 0 < Φ x ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hΦx))
  set W : ℝ := R / (2 * (1 - lam)) with hW_def
  have hWpos : 0 < W := by rw [hW_def]; positivity
  have hstat2 := stat_second_moment hP hπ heig hstep hlam2
  have hVπle : (∑ y, π y * Φ y ^ 2) ≤ W := by
    rw [hW_def, le_div_iff₀ (by linarith)]
    linarith
  have hVπpos : 0 < ∑ y, π y * Φ y ^ 2 := by
    obtain ⟨y0, hy0⟩ := Function.ne_iff.mp hΦ
    refine Finset.sum_pos' (fun i _ => mul_nonneg (hpos i).le (sq_nonneg _))
      ⟨y0, Finset.mem_univ y0, mul_pos (hpos y0)
        (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hy0)))⟩
  -- the mixing time is realised
  obtain ⟨α, ⟨hα0, hα1⟩, C, hC, hCd⟩ := MarkovMixing.convergence_theorem P hP hirr hap π hπ
  have hne : ∃ t : ℕ, MarkovMixing.distStationary P π t ≤ ε := by
    obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (div_pos hε hC) hα1
    refine ⟨t, ?_⟩
    have h2 : C * α ^ t < ε := by
      calc C * α ^ t < C * (ε / C) := mul_lt_mul_of_pos_left ht hC
        _ = ε := by field_simp
    linarith [hCd t]
  set T : ℕ := MarkovMixing.mixingTime P π ε with hT_def
  have hTmem : MarkovMixing.distStationary P π T ≤ ε := Nat.sInf_mem hne
  -- second moment along the chain
  set S : ℕ → ℝ := fun t => ∑ y, (P ^ t) x y * Φ y ^ 2 with hS_def
  have hrec : ∀ t : ℕ, S (t + 1) ≤ (2 * lam - 1) * S t + R := by
    intro t
    have e : ∑ y, (P ^ (t + 1)) x y * Φ y ^ 2
        = ∑ z, (P ^ t) x z * (∑ y, P z y * Φ y ^ 2) := by
      have e1 : ∀ y : V, (P ^ (t + 1)) x y * Φ y ^ 2
          = ∑ z, (P ^ t) x z * P z y * Φ y ^ 2 := by
        intro y
        rw [pow_succ, Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_congr rfl (fun y _ => e1 y), Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    show ∑ y, (P ^ (t + 1)) x y * Φ y ^ 2 ≤ (2 * lam - 1) * (∑ y, (P ^ t) x y * Φ y ^ 2) + R
    rw [e]
    calc ∑ z, (P ^ t) x z * (∑ y, P z y * Φ y ^ 2)
        ≤ ∑ z, (P ^ t) x z * ((2 * lam - 1) * Φ z ^ 2 + R) :=
          Finset.sum_le_sum fun z _ =>
            mul_le_mul_of_nonneg_left (onestep hP heig hstep z) ((pow_stochastic hP t).1 x z)
      _ = (2 * lam - 1) * (∑ z, (P ^ t) x z * Φ z ^ 2) + R := by
          have e2 : ∀ z : V, (P ^ t) x z * ((2 * lam - 1) * Φ z ^ 2 + R)
              = (2 * lam - 1) * ((P ^ t) x z * Φ z ^ 2) + R * (P ^ t) x z := fun z => by ring
          rw [Finset.sum_congr rfl (fun z _ => e2 z), Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum, (pow_stochastic hP t).2 x, mul_one]
  have hiter : ∀ t : ℕ, S t ≤ (2 * lam - 1) ^ t * Φ x ^ 2 + W := by
    intro t
    induction t with
    | zero =>
      have h0 : S 0 = Φ x ^ 2 := by
        show ∑ y, (P ^ 0) x y * Φ y ^ 2 = Φ x ^ 2
        rw [pow_zero]
        rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ x)
          (fun b _ hb => by rw [Matrix.one_apply_ne (Ne.symm hb)]; ring)]
        rw [Matrix.one_apply_eq]
        ring
      rw [h0]
      simp
      linarith [hWpos]
    | succ t ih =>
      have hc : 0 < 2 * lam - 1 := by linarith
      calc S (t + 1) ≤ (2 * lam - 1) * S t + R := hrec t
        _ ≤ (2 * lam - 1) * ((2 * lam - 1) ^ t * Φ x ^ 2 + W) + R := by nlinarith
        _ = (2 * lam - 1) ^ (t + 1) * Φ x ^ 2 + W := by
            have hne1 : (1:ℝ) - lam ≠ 0 := by linarith
            have hWid : (2 * lam - 1) * W + R = W := by
              rw [hW_def]
              field_simp
              ring
            calc (2 * lam - 1) * ((2 * lam - 1) ^ t * Φ x ^ 2 + W) + R
                = (2 * lam - 1) ^ (t + 1) * Φ x ^ 2 + ((2 * lam - 1) * W + R) := by ring
              _ = (2 * lam - 1) ^ (t + 1) * Φ x ^ 2 + W := by rw [hWid]
  have hmean : ∀ t : ℕ, MarkovMixing.distExp (MarkovMixing.rowDist P t x) Φ = lam ^ t * Φ x := by
    intro t
    have h := congrFun (mulVec_pow_eig heig t) x
    show ∑ y, Φ y * (P ^ t) x y = lam ^ t * Φ x
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [← h]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hexpπ : MarkovMixing.distExp π Φ = 0 := eig_orthogonal hπ heig (by linarith)
  have hVπeq : MarkovMixing.distVar π Φ = ∑ y, π y * Φ y ^ 2 := by
    rw [distVar_eq hπ.1 Φ, hexpπ]
    have : (0:ℝ) ^ 2 = 0 := by norm_num
    rw [this, sub_zero]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hvarT : MarkovMixing.distVar (MarkovMixing.rowDist P T x) Φ ≤ W := by
    rw [distVar_eq (pow_isDist hP T x) Φ, hmean T]
    have hSeq : ∑ y, Φ y ^ 2 * MarkovMixing.rowDist P T x y = S T := by
      show ∑ y, Φ y ^ 2 * (P ^ T) x y = ∑ y, (P ^ T) x y * Φ y ^ 2
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [hSeq]
    have h1 := hiter T
    have h2 : (2 * lam - 1) ^ T ≤ (lam ^ 2) ^ T :=
      pow_le_pow_left₀ (by linarith) (by nlinarith [sq_nonneg (lam - 1)]) T
    have h3 : (lam ^ 2) ^ T = (lam ^ T) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
    nlinarith [sq_nonneg (Φ x)]
  -- apply the corrected Proposition 7.8
  have hVarnn := distVar_nonneg (pow_isDist hP T x) Φ
  have hσ2pos : 0 < MarkovMixing.distVar (MarkovMixing.rowDist P T x) Φ
      + MarkovMixing.distVar π Φ := by rw [hVπeq]; linarith
  have hσ2le : (MarkovMixing.distVar (MarkovMixing.rowDist P T x) Φ
      + MarkovMixing.distVar π Φ) / 2 ≤ W := by rw [hVπeq]; linarith
  set r0 : ℝ := lam ^ T * |Φ x| * Real.sqrt (2 * (1 - lam) / R) with hr0_def
  have hr0nn : 0 ≤ r0 := by
    rw [hr0_def]
    have h1 : (0:ℝ) ≤ Real.sqrt (2 * (1 - lam) / R) := Real.sqrt_nonneg _
    have h2 : (0:ℝ) < lam ^ T := pow_pos hlam0 T
    have h3 : (0:ℝ) ≤ |Φ x| := abs_nonneg _
    positivity
  have hprod : Real.sqrt (2 * (1 - lam) / R) * Real.sqrt W = 1 := by
    rw [← Real.sqrt_mul (by positivity)]
    have e : 2 * (1 - lam) / R * W = 1 := by
      rw [hW_def]
      have hne1 : (1:ℝ) - lam ≠ 0 := by linarith
      field_simp
    rw [e, Real.sqrt_one]
  have hsep : r0 * Real.sqrt ((MarkovMixing.distVar (MarkovMixing.rowDist P T x) Φ
        + MarkovMixing.distVar π Φ) / 2)
      ≤ |MarkovMixing.distExp (MarkovMixing.rowDist P T x) Φ - MarkovMixing.distExp π Φ| := by
    rw [hmean T, hexpπ, sub_zero, abs_mul, abs_pow, abs_of_pos hlam0]
    calc r0 * Real.sqrt ((MarkovMixing.distVar (MarkovMixing.rowDist P T x) Φ
          + MarkovMixing.distVar π Φ) / 2)
        ≤ r0 * Real.sqrt W := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hσ2le) hr0nn
      _ = lam ^ T * |Φ x| := by rw [hr0_def, mul_assoc, hprod, mul_one]
  have h78 := MarkovMixing.distinguishing_statistic_of_pos_variance
    (MarkovMixing.rowDist P T x) π (pow_isDist hP T x) hπ.1 Φ hσ2pos r0 hr0nn hsep
  have htv : MarkovMixing.tvDist (MarkovMixing.rowDist P T x) π ≤ ε :=
    le_trans (le_distStationary P π T x) hTmem
  have h1 : 1 - 4 / (4 + r0 ^ 2) ≤ ε := le_trans h78 htv
  have hr0sq : r0 ^ 2 * (1 - ε) ≤ 4 * ε := by
    have h2 : (0:ℝ) < 4 + r0 ^ 2 := by positivity
    have h3 : r0 ^ 2 / (4 + r0 ^ 2) ≤ ε := by
      have e : 1 - 4 / (4 + r0 ^ 2) = r0 ^ 2 / (4 + r0 ^ 2) := by field_simp; ring
      rw [← e]; exact h1
    rw [div_le_iff₀ h2] at h3
    nlinarith
  have hr0sq_eq : r0 ^ 2 = (lam ^ T) ^ 2 * Φ x ^ 2 * (2 * (1 - lam) / R) := by
    rw [hr0_def, mul_pow, mul_pow, Real.sq_sqrt (by positivity), sq_abs]
  -- logarithms
  set D : ℝ := (1 - lam) * Φ x ^ 2 / (2 * R) with hD_def
  set G : ℝ := (1 - ε) / ε with hG_def
  have hDpos : 0 < D := by rw [hD_def]; positivity
  have hGpos : 0 < G := by rw [hG_def]; positivity
  have hkey : (lam ^ T) ^ 2 * (D * G) ≤ 1 := by
    have h4 : (0:ℝ) < 4 * ε := by linarith
    have e : (lam ^ T) ^ 2 * (D * G) * (4 * ε) = r0 ^ 2 * (1 - ε) := by
      rw [hr0sq_eq, hD_def, hG_def]
      field_simp
      ring
    have h7 : (lam ^ T) ^ 2 * (D * G) * (4 * ε) ≤ 1 * (4 * ε) := by
      rw [e, one_mul]
      exact hr0sq
    exact le_of_mul_le_mul_right h7 h4
  have hLpos : 0 < Real.log (1 / lam) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hlam0]
    linarith
  have hlog : Real.log D + Real.log G ≤ 2 * Real.log (1 / lam) * (T : ℝ) := by
    have h5 : Real.log ((lam ^ T) ^ 2 * (D * G)) ≤ 0 := by
      rw [← Real.log_one]
      exact Real.log_le_log (by positivity) hkey
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hDpos.ne' hGpos.ne',
      Real.log_pow, Real.log_pow] at h5
    have h6 : Real.log (1 / lam) = -Real.log lam := by rw [one_div, Real.log_inv]
    rw [h6]
    push_cast at h5 ⊢
    linarith
  calc (2 * Real.log (1 / lam))⁻¹ * (Real.log D + Real.log G)
      ≤ (2 * Real.log (1 / lam))⁻¹ * (2 * Real.log (1 / lam) * (T : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = (T : ℝ) := by
        field_simp
