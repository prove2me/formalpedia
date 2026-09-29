-- Prove2me | solution 1 for BanditAlgorithm.linear_bandit_linucb_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T17:08:23.445384+00:00
-- url     : https://prove2.me/submissions/825d42cb-1a71-4e2a-8b2e-70fffe405640

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic
import Definitions.Def_StochasticLinearBandit

open Matrix

namespace BanditAlgorithm

private lemma det_add_vecMulVec {d : ℕ}
    (V : Matrix (Fin d) (Fin d) ℝ) (hV : V.PosDef) (u : Fin d → ℝ) :
    (V + vecMulVec u u).det =
      V.det * (1 + u ⬝ᵥ V⁻¹ *ᵥ u) := by
  rw [vecMulVec_eq Unit,
    Matrix.det_add_replicateCol_mul_replicateRow
      (hV.isUnit.map Matrix.detMonoidHom)]
  congr 2
  rw [Matrix.det_unique]
  change
    (1 + ∑ j, (∑ i, u i * V⁻¹ i j) * u j) =
      1 + ∑ i, u i * ∑ j, V⁻¹ i j * u j
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma regularizedDesignMatrixSeq_zero {d : ℕ} (lam : ℝ)
    (a : ℕ → Fin d → ℝ) :
    regularizedDesignMatrixSeq d lam a 0 =
      lam • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  simp [regularizedDesignMatrixSeq, regularizedDesignMatrix]

private lemma regularizedDesignMatrixSeq_succ {d t : ℕ} (lam : ℝ)
    (a : ℕ → Fin d → ℝ) :
    regularizedDesignMatrixSeq d lam a (t + 1) =
      regularizedDesignMatrixSeq d lam a t +
        vecMulVec (a (t + 1)) (a (t + 1)) := by
  simp only [regularizedDesignMatrixSeq, regularizedDesignMatrix,
    Finset.sum_range_succ, Finset.sum_const_zero, Finset.sum_add_distrib]
  abel

private lemma regularizedDesignMatrixSeq_posDef {d t : ℕ} {lam : ℝ}
    (hlam : 0 < lam) (a : ℕ → Fin d → ℝ) :
    (regularizedDesignMatrixSeq d lam a t).PosDef := by
  rw [regularizedDesignMatrixSeq, regularizedDesignMatrix]
  exact (Matrix.PosDef.one.smul hlam).add_posSemidef
    (Matrix.posSemidef_sum (Finset.range t)
      fun _ _ ↦ by simpa using Matrix.posSemidef_vecMulVec_self_star _)

private lemma min_one_le_two_log_one_add {u : ℝ} (hu : 0 ≤ u) :
    min 1 u ≤ 2 * Real.log (1 + u) := by
  have hden : 0 < u + 2 := by linarith
  have hseries := Real.le_log_one_add_of_nonneg hu
  have hmid : min 1 u ≤ 4 * u / (u + 2) := by
    rw [le_div_iff₀ hden]
    by_cases h : u ≤ 1
    · rw [min_eq_right h]
      nlinarith
    · rw [min_eq_left (le_of_not_ge h)]
      nlinarith
  calc
    min 1 u ≤ 4 * u / (u + 2) := hmid
    _ ≤ 2 * Real.log (1 + u) := by
      convert mul_le_mul_of_nonneg_left hseries (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring

private lemma log_det_ratio_eq_sum {d n : ℕ} {lam : ℝ}
    (hlam : 0 < lam) (a : ℕ → Fin d → ℝ) :
    Real.log
        ((regularizedDesignMatrixSeq d lam a n).det /
          (regularizedDesignMatrixSeq d lam a 0).det) =
      ∑ t ∈ Finset.range n,
        Real.log
          (1 + a (t + 1) ⬝ᵥ
            (regularizedDesignMatrixSeq d lam a t)⁻¹ *ᵥ a (t + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      let V := regularizedDesignMatrixSeq d lam a n
      let u := a (n + 1)
      have hV : V.PosDef := regularizedDesignMatrixSeq_posDef hlam a
      have hV0 : (regularizedDesignMatrixSeq d lam a 0).PosDef :=
        regularizedDesignMatrixSeq_posDef hlam a
      have hq : 0 ≤ u ⬝ᵥ V⁻¹ *ᵥ u := by
        simpa using hV.inv.posSemidef.dotProduct_mulVec_nonneg u
      have hdet :
          (regularizedDesignMatrixSeq d lam a (n + 1)).det =
            V.det * (1 + u ⬝ᵥ V⁻¹ *ᵥ u) := by
        rw [regularizedDesignMatrixSeq_succ]
        exact det_add_vecMulVec V hV u
      rw [hdet]
      have hratio :
          V.det * (1 + u ⬝ᵥ V⁻¹ *ᵥ u) /
              (regularizedDesignMatrixSeq d lam a 0).det =
            (V.det / (regularizedDesignMatrixSeq d lam a 0).det) *
              (1 + u ⬝ᵥ V⁻¹ *ᵥ u) := by ring
      rw [hratio, Real.log_mul]
      · rw [ih, Finset.sum_range_succ]
      · exact div_ne_zero hV.det_pos.ne' hV0.det_pos.ne'
      · positivity

private lemma elliptical_sum_le_log_det {d n : ℕ} {lam : ℝ}
    (hlam : 0 < lam) (a : ℕ → Fin d → ℝ) :
    ∑ t ∈ Finset.range n,
        min 1 (a (t + 1) ⬝ᵥ
          (regularizedDesignMatrixSeq d lam a t)⁻¹ *ᵥ a (t + 1)) ≤
      2 * Real.log
        ((regularizedDesignMatrixSeq d lam a n).det /
          (regularizedDesignMatrixSeq d lam a 0).det) := by
  rw [log_det_ratio_eq_sum hlam a, Finset.mul_sum]
  gcongr with t ht
  exact min_one_le_two_log_one_add <| by
    simpa using
      (regularizedDesignMatrixSeq_posDef (t := t) hlam a).inv.posSemidef
        |>.dotProduct_mulVec_nonneg (a (t + 1))

private lemma det_le_pow_trace_div {d : ℕ} (hd : 0 < d)
    {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) :
    V.det ≤ (V.trace / d) ^ d := by
  let e : Fin d → ℝ := hV.isHermitian.eigenvalues
  have he : ∀ i ∈ (Finset.univ : Finset (Fin d)), 0 ≤ e i :=
    fun i _ ↦ hV.eigenvalues_pos i |>.le
  have hamgm := Real.geom_mean_le_arith_mean
    (Finset.univ : Finset (Fin d)) (fun _ : Fin d ↦ (1 : ℝ)) e
    (by simp) (by simpa using (Nat.cast_pos.mpr hd)) he
  simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hamgm
  change
    (∏ i, hV.isHermitian.eigenvalues i) ^ ((d : ℝ)⁻¹) ≤
      (∑ i, hV.isHermitian.eigenvalues i) / d at hamgm
  have hdet : V.det = ∏ i, hV.isHermitian.eigenvalues i := by
    simpa using hV.isHermitian.det_eq_prod_eigenvalues
  have htrace : V.trace = ∑ i, hV.isHermitian.eigenvalues i := by
    simpa using hV.isHermitian.trace_eq_sum_eigenvalues
  rw [← hdet, ← htrace] at hamgm
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg hV.det_pos.le _) hamgm d
  simpa [Real.rpow_inv_natCast_pow hV.det_pos.le (Nat.ne_of_gt hd)] using hp

private lemma regularizedDesignMatrixSeq_trace {d n : ℕ} (lam : ℝ)
    (a : ℕ → Fin d → ℝ) :
    (regularizedDesignMatrixSeq d lam a n).trace =
      d * lam + ∑ t ∈ Finset.range n, a (t + 1) ⬝ᵥ a (t + 1) := by
  simp [regularizedDesignMatrixSeq, regularizedDesignMatrix,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum,
    Matrix.trace_vecMulVec, Matrix.trace_one, Fintype.card_fin]
  ring

private lemma regularizedDesignMatrixSeq_trace_le {d n : ℕ} (lam L : ℝ)
    (a : ℕ → Fin d → ℝ)
    (ha : ∀ t ∈ Finset.range n,
      Real.sqrt (a (t + 1) ⬝ᵥ a (t + 1)) ≤ L) :
    (regularizedDesignMatrixSeq d lam a n).trace ≤ d * lam + n * L ^ 2 := by
  rw [regularizedDesignMatrixSeq_trace]
  gcongr
  calc
    ∑ t ∈ Finset.range n, a (t + 1) ⬝ᵥ a (t + 1)
        ≤ ∑ _t ∈ Finset.range n, L ^ 2 := by
          gcongr with t ht
          have hq : 0 ≤ a (t + 1) ⬝ᵥ a (t + 1) := by
            exact Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _
          have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) (ha t ht) 2
          simpa [Real.sq_sqrt hq] using hs
    _ = n * L ^ 2 := by simp

private lemma regularized_log_det_ratio_le {d n : ℕ} (hd : 0 < d)
    {lam L : ℝ} (hlam : 0 < lam) (a : ℕ → Fin d → ℝ)
    (ha : ∀ t ∈ Finset.range n,
      Real.sqrt (a (t + 1) ⬝ᵥ a (t + 1)) ≤ L) :
    Real.log
        ((regularizedDesignMatrixSeq d lam a n).det /
          (regularizedDesignMatrixSeq d lam a 0).det) ≤
      d * Real.log ((d * lam + n * L ^ 2) / (d * lam)) := by
  let V := regularizedDesignMatrixSeq d lam a n
  have hV : V.PosDef := regularizedDesignMatrixSeq_posDef hlam a
  have hV0 : (regularizedDesignMatrixSeq d lam a 0).PosDef :=
    regularizedDesignMatrixSeq_posDef hlam a
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have htrace := regularizedDesignMatrixSeq_trace_le lam L a ha
  have havg :
      V.trace / d ≤ (d * lam + n * L ^ 2) / d :=
    div_le_div_of_nonneg_right htrace hdR.le
  have havg0 : 0 ≤ V.trace / d := by
    exact div_nonneg hV.trace_pos.le hdR.le
  have hdet :
      V.det ≤ ((d * lam + n * L ^ 2) / d) ^ d :=
    (det_le_pow_trace_div hd hV).trans
      (pow_le_pow_left₀ havg0 havg d)
  have hdet0 :
      (regularizedDesignMatrixSeq d lam a 0).det = lam ^ d := by
    rw [regularizedDesignMatrixSeq_zero, Matrix.det_smul,
      Fintype.card_fin, Matrix.det_one, mul_one]
  have hden : 0 < lam ^ d := pow_pos hlam d
  have hratio :
      V.det / (regularizedDesignMatrixSeq d lam a 0).det ≤
        ((d * lam + n * L ^ 2) / (d * lam)) ^ d := by
    have hrhs :
        ((d * lam + n * L ^ 2) / (d * lam)) ^ d =
          (((d * lam + n * L ^ 2) / d) ^ d) / lam ^ d := by
      rw [div_pow, div_pow, mul_pow]
      field_simp
    rw [hdet0, hrhs]
    exact (div_le_div_iff_of_pos_right hden).2 hdet
  have hleft :
      0 < V.det / (regularizedDesignMatrixSeq d lam a 0).det :=
    div_pos hV.det_pos hV0.det_pos
  have hbase :
      0 < (d * lam + n * L ^ 2) / (d * lam) := by
    have hdl : 0 < (d : ℝ) * lam := mul_pos hdR hlam
    have hnL : 0 ≤ (n : ℝ) * L ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    exact div_pos (add_pos_of_pos_of_nonneg hdl hnL) hdl
  have hlog := Real.log_le_log hleft hratio
  simpa [Real.log_pow] using hlog

private lemma inverse_weighted_cauchy {d : ℕ}
    {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef)
    (a w : Fin d → ℝ) :
    (a ⬝ᵥ w) ^ 2 ≤
      (a ⬝ᵥ V⁻¹ *ᵥ a) * (w ⬝ᵥ V *ᵥ w) := by
  let B := Matrix.toBilin' V⁻¹
  have hBnonneg : ∀ z, 0 ≤ B z z := by
    intro z
    simpa [B, Matrix.toBilin'_apply'] using
      hV.inv.posSemidef.dotProduct_mulVec_nonneg z
  have hBsymm : LinearMap.IsSymm B := by
    constructor
    intro z y
    simp only [B, Matrix.toBilin'_apply', RingHom.id_apply,
      dotProduct, Matrix.mulVec]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hsymm : V⁻¹ i j = V⁻¹ j i := by
      simpa using hV.inv.isHermitian.apply j i
    rw [hsymm]
    ring
  have hcs := B.apply_sq_le_of_symm hBnonneg hBsymm a (V *ᵥ w)
  have hcancel : V⁻¹ *ᵥ (V *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul V (hV.isUnit.map Matrix.detMonoidHom),
      Matrix.one_mulVec]
  simpa [B, Matrix.toBilin'_apply', hcancel, dotProduct_comm] using hcs

private lemma ellipsoid_pair_distance {d : ℕ}
    {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef)
    (center θ₁ θ₂ : Fin d → ℝ) (β : ℝ)
    (h₁ : (center - θ₁) ⬝ᵥ V *ᵥ (center - θ₁) ≤ β)
    (h₂ : (center - θ₂) ⬝ᵥ V *ᵥ (center - θ₂) ≤ β) :
    (θ₁ - θ₂) ⬝ᵥ V *ᵥ (θ₁ - θ₂) ≤ 4 * β := by
  let p := center - θ₁
  let q := center - θ₂
  let Q := fun z : Fin d → ℝ ↦ z ⬝ᵥ V *ᵥ z
  have hsum : 0 ≤ Q (p + q) := by
    simpa [Q] using hV.posSemidef.dotProduct_mulVec_nonneg (p + q)
  have hsymm : p ⬝ᵥ V *ᵥ q = q ⬝ᵥ V *ᵥ p := by
    simp only [dotProduct, Matrix.mulVec]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hVij : V i j = V j i := by
      simpa using hV.isHermitian.apply j i
    rw [hVij]
    ring
  have hid : Q (q - p) + Q (p + q) = 2 * Q p + 2 * Q q := by
    simp only [Q, Matrix.mulVec_sub, Matrix.mulVec_add, sub_dotProduct,
      add_dotProduct, dotProduct_sub, dotProduct_add]
    rw [hsymm]
    ring
  have hqp : Q (q - p) ≤ 2 * Q p + 2 * Q q := by
    nlinarith
  have hp : Q p ≤ β := by simpa [Q, p] using h₁
  have hq : Q q ≤ β := by simpa [Q, q] using h₂
  have hdiff : q - p = θ₁ - θ₂ := by
    ext i
    simp [p, q]
  rw [← hdiff]
  exact hqp.trans (by linarith)

private lemma linucb_round_regret_sq_le {d n t : ℕ} (hn : 0 < n)
    {lam : ℝ} (hlam : 0 < lam)
    (𝓐 𝓒 : ℕ → Set (Fin d → ℝ)) (β : ℕ → ℝ)
    (a θtilde astar : ℕ → Fin d → ℝ) (x : ℕ → ℝ)
    (θstar : Fin d → ℝ)
    (hβ_one : 1 ≤ β 1)
    (hβ_mono : ∀ s u : ℕ, 1 ≤ s → s ≤ u → u ≤ n → β s ≤ β u)
    (hb : ∀ u ∈ Finset.range n, ∀ b ∈ 𝓐 (u + 1), ∀ b' ∈ 𝓐 (u + 1),
      θstar ⬝ᵥ (b - b') ≤ 1)
    (htrace : IsLinUCBTrace lam n 𝓐 𝓒 β a θtilde astar x θstar)
    (hmem : ∀ u ∈ Finset.range n, θstar ∈ 𝓒 (u + 1))
    (ht : t ∈ Finset.range n) :
    ((astar (t + 1) - a (t + 1)) ⬝ᵥ θstar) ^ 2 ≤
      4 * β n *
        min 1 (a (t + 1) ⬝ᵥ
          (regularizedDesignMatrixSeq d lam a t)⁻¹ *ᵥ a (t + 1)) := by
  rcases htrace t ht with
    ⟨hsubset, haA, hthetaC, hopt, hastarA, hastaropt⟩
  let V := regularizedDesignMatrixSeq d lam a t
  let center := regularizedLeastSquaresSeq d lam a x t
  let act := a (t + 1)
  let rt := (astar (t + 1) - act) ⬝ᵥ θstar
  let w := θtilde (t + 1) - θstar
  let q := act ⬝ᵥ V⁻¹ *ᵥ act
  have htn : t + 1 ≤ n := Finset.mem_range.mp ht
  have hβn : 1 ≤ β n :=
    hβ_one.trans (hβ_mono 1 n (by omega) (by omega) (by omega))
  have hβt : β (t + 1) ≤ β n :=
    hβ_mono (t + 1) n (by omega) htn (by omega)
  have hV : V.PosDef := regularizedDesignMatrixSeq_posDef hlam a
  have hq : 0 ≤ q := by
    simpa [q, act, V] using hV.inv.posSemidef.dotProduct_mulVec_nonneg act
  have hθstarC := hmem t ht
  have hoptstar := hopt (astar (t + 1)) hastarA θstar hθstarC
  have hr_upper : rt ≤ act ⬝ᵥ w := by
    calc
      rt = astar (t + 1) ⬝ᵥ θstar - act ⬝ᵥ θstar := by
        simp [rt, sub_dotProduct]
      _ ≤ act ⬝ᵥ θtilde (t + 1) - act ⬝ᵥ θstar :=
        sub_le_sub_right hoptstar _
      _ = act ⬝ᵥ w := by simp [w, dotProduct_sub]
  have hplayed_opt := hastaropt act haA
  have hr_nonneg : 0 ≤ rt := by
    rw [show rt = astar (t + 1) ⬝ᵥ θstar - act ⬝ᵥ θstar by
      simp [rt, sub_dotProduct]]
    exact sub_nonneg.mpr hplayed_opt
  have hr_one : rt ≤ 1 := by
    simpa [rt, act, dotProduct_comm] using hb t ht (astar (t + 1)) hastarA act haA
  have hθtildeE := hsubset hthetaC
  have hθstarE := hsubset hθstarC
  change (center - θtilde (t + 1)) ⬝ᵥ V *ᵥ
      (center - θtilde (t + 1)) ≤ β (t + 1) at hθtildeE
  change (center - θstar) ⬝ᵥ V *ᵥ
      (center - θstar) ≤ β (t + 1) at hθstarE
  have hdist :
      w ⬝ᵥ V *ᵥ w ≤ 4 * β n := by
    have hpair := ellipsoid_pair_distance hV center (θtilde (t + 1))
      θstar (β (t + 1)) hθtildeE hθstarE
    exact hpair.trans (by linarith)
  have hcs := inverse_weighted_cauchy hV act w
  have hr_sq_le_aw : rt ^ 2 ≤ (act ⬝ᵥ w) ^ 2 := by
    nlinarith
  have hr_sq_le_q : rt ^ 2 ≤ 4 * β n * q := by
    calc
      rt ^ 2 ≤ (act ⬝ᵥ w) ^ 2 := hr_sq_le_aw
      _ ≤ q * (w ⬝ᵥ V *ᵥ w) := by simpa [q, act] using hcs
      _ ≤ q * (4 * β n) := mul_le_mul_of_nonneg_left hdist hq
      _ = 4 * β n * q := by ring
  by_cases hq1 : q ≤ 1
  · rw [min_eq_right hq1]
    exact hr_sq_le_q
  · rw [min_eq_left (le_of_not_ge hq1)]
    nlinarith [sq_nonneg rt]

private lemma linucb_regret_le_elliptical_sqrt {d n : ℕ} (hn : 0 < n)
    {lam : ℝ} (hlam : 0 < lam)
    (𝓐 𝓒 : ℕ → Set (Fin d → ℝ)) (β : ℕ → ℝ)
    (a θtilde astar : ℕ → Fin d → ℝ) (x : ℕ → ℝ)
    (θstar : Fin d → ℝ)
    (hβ_one : 1 ≤ β 1)
    (hβ_mono : ∀ s t : ℕ, 1 ≤ s → s ≤ t → t ≤ n → β s ≤ β t)
    (hb : ∀ t ∈ Finset.range n, ∀ b ∈ 𝓐 (t + 1), ∀ b' ∈ 𝓐 (t + 1),
      θstar ⬝ᵥ (b - b') ≤ 1)
    (htrace : IsLinUCBTrace lam n 𝓐 𝓒 β a θtilde astar x θstar)
    (hmem : ∀ t ∈ Finset.range n, θstar ∈ 𝓒 (t + 1)) :
    linearPseudoRegret θstar a astar n ≤
      Real.sqrt
        (4 * n * β n *
          ∑ t ∈ Finset.range n,
            min 1 (a (t + 1) ⬝ᵥ
              (regularizedDesignMatrixSeq d lam a t)⁻¹ *ᵥ a (t + 1))) := by
  let r := fun t : ℕ ↦ (astar (t + 1) - a (t + 1)) ⬝ᵥ θstar
  let q := fun t : ℕ ↦ a (t + 1) ⬝ᵥ
    (regularizedDesignMatrixSeq d lam a t)⁻¹ *ᵥ a (t + 1)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.range n) (fun _t : ℕ ↦ (1 : ℝ)) r
  have hcs' :
      (∑ t ∈ Finset.range n, r t) ^ 2 ≤
        n * ∑ t ∈ Finset.range n, (r t) ^ 2 := by
    simpa using hcs
  have hsum :
      ∑ t ∈ Finset.range n, (r t) ^ 2 ≤
        ∑ t ∈ Finset.range n, 4 * β n * min 1 (q t) := by
    gcongr with t ht
    simpa [r, q] using linucb_round_regret_sq_le hn hlam 𝓐 𝓒 β
      a θtilde astar x θstar hβ_one hβ_mono hb htrace hmem ht
  have hsq :
      (∑ t ∈ Finset.range n, r t) ^ 2 ≤
        4 * n * β n * ∑ t ∈ Finset.range n, min 1 (q t) := by
    calc
      (∑ t ∈ Finset.range n, r t) ^ 2
          ≤ n * ∑ t ∈ Finset.range n, (r t) ^ 2 := hcs'
      _ ≤ n * ∑ t ∈ Finset.range n, 4 * β n * min 1 (q t) :=
        mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg n)
      _ = 4 * n * β n * ∑ t ∈ Finset.range n, min 1 (q t) := by
        simp_rw [← Finset.mul_sum]
        ring
  simpa [linearPseudoRegret, r, q] using Real.le_sqrt_of_sq_le hsq

end BanditAlgorithm

open BanditAlgorithm

theorem solution {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {lam L : ℝ} (hlam : 0 < lam)
    (𝓐 𝓒 : ℕ → Set (Fin d → ℝ)) (β : ℕ → ℝ)
    (a θtilde astar : ℕ → Fin d → ℝ) (x : ℕ → ℝ) (θstar : Fin d → ℝ)
    (hβ_one : 1 ≤ β 1)
    (hβ_mono : ∀ s t : ℕ, 1 ≤ s → s ≤ t → t ≤ n → β s ≤ β t)
    (hb : ∀ t ∈ Finset.range n, ∀ b ∈ 𝓐 (t + 1), ∀ b' ∈ 𝓐 (t + 1),
      θstar ⬝ᵥ (b - b') ≤ 1)
    (hL : ∀ t ∈ Finset.range n, ∀ b ∈ 𝓐 (t + 1),
      Real.sqrt (b ⬝ᵥ b) ≤ L)
    (htrace : IsLinUCBTrace lam n 𝓐 𝓒 β a θtilde astar x θstar)
    (hmem : ∀ t ∈ Finset.range n, θstar ∈ 𝓒 (t + 1)) :
    linearPseudoRegret θstar a astar n ≤
      Real.sqrt (8 * n * β n *
        Real.log ((regularizedDesignMatrixSeq d lam a n).det /
          (regularizedDesignMatrixSeq d lam a 0).det)) ∧
    Real.sqrt (8 * n * β n *
        Real.log ((regularizedDesignMatrixSeq d lam a n).det /
          (regularizedDesignMatrixSeq d lam a 0).det)) ≤
      Real.sqrt (8 * d * n * β n *
        Real.log ((d * lam + n * L ^ 2) / (d * lam))) := by
  have ha :
      ∀ t ∈ Finset.range n,
        Real.sqrt (a (t + 1) ⬝ᵥ a (t + 1)) ≤ L := by
    intro t ht
    exact hL t ht (a (t + 1)) (htrace t ht).2.1
  have hβn : 0 ≤ β n := by
    have : 1 ≤ β n :=
      hβ_one.trans (hβ_mono 1 n (by omega) (by omega) (by omega))
    linarith
  have hcoeff : 0 ≤ 4 * (n : ℝ) * β n := by positivity
  have hregret := BanditAlgorithm.linucb_regret_le_elliptical_sqrt
    hn hlam 𝓐 𝓒 β a θtilde astar x θstar hβ_one hβ_mono hb htrace hmem
  have hpot := BanditAlgorithm.elliptical_sum_le_log_det (n := n) hlam a
  have hfirstInside :
      4 * n * β n *
          (∑ t ∈ Finset.range n,
            min 1 (a (t + 1) ⬝ᵥ
              (regularizedDesignMatrixSeq d lam a t)⁻¹ *ᵥ a (t + 1))) ≤
        8 * n * β n *
          Real.log ((regularizedDesignMatrixSeq d lam a n).det /
            (regularizedDesignMatrixSeq d lam a 0).det) := by
    have := mul_le_mul_of_nonneg_left hpot hcoeff
    nlinarith
  have hfirst :
      linearPseudoRegret θstar a astar n ≤
        Real.sqrt (8 * n * β n *
          Real.log ((regularizedDesignMatrixSeq d lam a n).det /
            (regularizedDesignMatrixSeq d lam a 0).det)) :=
    hregret.trans (Real.sqrt_le_sqrt hfirstInside)
  have hlog := BanditAlgorithm.regularized_log_det_ratio_le hd hlam a ha
  have hsecondInside :
      8 * n * β n *
          Real.log ((regularizedDesignMatrixSeq d lam a n).det /
            (regularizedDesignMatrixSeq d lam a 0).det) ≤
        8 * d * n * β n *
          Real.log ((d * lam + n * L ^ 2) / (d * lam)) := by
    have hscale : 0 ≤ 8 * (n : ℝ) * β n := by positivity
    have := mul_le_mul_of_nonneg_left hlog hscale
    nlinarith
  exact ⟨hfirst, Real.sqrt_le_sqrt hsecondInside⟩
