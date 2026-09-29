-- Prove2me | solution 1 for LinearOptimization.ellipsoid_update_volume_lt
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-09T17:35:08.989891+00:00
-- url     : https://prove2.me/submissions/7227695c-06a8-4471-9b18-f667458fdcd2

import Definitions.Def_LinearOptimization_EllipsoidMethod
import Theorems.Thm_LinearOptimization_ellipsoid_update_matrix_posDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

open Matrix MeasureTheory LinearOptimization
open scoped MatrixOrder

private def quadBall (n : ℕ) : Set (Fin n → ℝ) :=
  {x | x ⬝ᵥ x ≤ 1}

private theorem measurable_quadBall (n : ℕ) : MeasurableSet (quadBall n) := by
  apply IsClosed.measurableSet
  change IsClosed ((fun x : Fin n → ℝ => x ⬝ᵥ x) ⁻¹' Set.Iic 1)
  exact isClosed_Iic.preimage (by fun_prop)

private theorem volume_quadBall_pos {n : ℕ} [Nonempty (Fin n)] :
    0 < volume (quadBall n) := by
  let U : Set (Fin n → ℝ) := {x | x ⬝ᵥ x < 1}
  have hUopen : IsOpen U := by
    change IsOpen ((fun x : Fin n → ℝ => x ⬝ᵥ x) ⁻¹' Set.Iio 1)
    exact isOpen_Iio.preimage (by fun_prop)
  have hUne : U.Nonempty := by
    refine ⟨0, ?_⟩
    simp [U, dotProduct]
  exact (hUopen.measure_pos volume hUne).trans_le <|
    measure_mono fun x hx => by
      change x ⬝ᵥ x < 1 at hx
      exact le_of_lt hx

private theorem volume_quadBall_lt_top {n : ℕ} :
    volume (quadBall n) < ⊤ := by
  apply IsCompact.measure_lt_top
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · change IsClosed ((fun x : Fin n → ℝ => x ⬝ᵥ x) ⁻¹' Set.Iic 1)
    exact isClosed_Iic.preimage (by fun_prop)
  · apply Metric.isBounded_closedBall.subset
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).2
    intro i
    rw [Real.norm_eq_abs, abs_le]
    change x ⬝ᵥ x ≤ 1 at hx
    have hterm : x i ^ 2 ≤ x ⬝ᵥ x := by
      change x i ^ 2 ≤ ∑ j, x j * x j
      rw [sq]
      exact Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
    constructor <;> nlinarith

private theorem ellipsoid_eq_preimage_invS {n : ℕ} (z : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef) :
    ellipsoid z D =
      (fun x => (CFC.sqrt D)⁻¹.mulVec (x - z)) ⁻¹' quadBall n := by
  classical
  let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt D
  have hSsymm : S⁻¹ᵀ = S⁻¹ := by
    simpa [S, Matrix.IsHermitian, Matrix.conjTranspose_apply] using
      ((CFC.sqrt_nonneg D).posSemidef.isHermitian.inv.eq)
  have hDinvsq : D⁻¹ = S⁻¹ * S⁻¹ := by
    rw [← CFC.sq_sqrt D hD.posSemidef.nonneg]
    change (S ^ 2)⁻¹ = S⁻¹ * S⁻¹
    rw [← Matrix.inv_pow']
    simp [pow_two]
  ext x
  change ((x - z) ⬝ᵥ D⁻¹.mulVec (x - z) ≤ 1) ↔
    (S⁻¹.mulVec (x - z) ⬝ᵥ S⁻¹.mulVec (x - z) ≤ 1)
  rw [hDinvsq, ← Matrix.mulVec_mulVec]
  have hv : (x - z) ᵥ* S⁻¹ = S⁻¹ᵀ.mulVec (x - z) := by
    simpa using Matrix.vecMul_transpose S⁻¹ᵀ (x - z)
  rw [Matrix.dotProduct_mulVec, hv, hSsymm]

theorem ellipsoid_volume_formula {n : ℕ} (z : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef) :
    volume (ellipsoid z D) =
      ENNReal.ofReal (Real.sqrt D.det) * volume (quadBall n) := by
  classical
  let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt D
  have hSdet : S.det = Real.sqrt D.det := by
    simpa [S] using hD.posSemidef.det_sqrt
  have hdetpos : 0 < D.det := hD.det_pos
  have hSdetpos : 0 < S.det := by rw [hSdet]; positivity
  have hSinvdet : S⁻¹.det ≠ 0 := by
    have hsqrt0 : Real.sqrt D.det ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hdetpos)
    simp [Matrix.det_nonsing_inv, hSdet, hsqrt0]
  rw [ellipsoid_eq_preimage_invS z D hD]
  -- Translation by `z` does not change volume.
  have htranslate :
      volume ((fun x => S⁻¹.mulVec (x - z)) ⁻¹' quadBall n) =
        volume ((fun x => S⁻¹.mulVec x) ⁻¹' quadBall n) := by
    let A : Set (Fin n → ℝ) := (fun x => S⁻¹.mulVec x) ⁻¹' quadBall n
    have hset :
        (fun x => S⁻¹.mulVec (x - z)) ⁻¹' quadBall n =
          (fun x => x + (-z)) ⁻¹' A := by
      ext x
      simp only [Set.mem_preimage, A]
      simp [sub_eq_add_neg]
    rw [hset, measure_preimage_add_right]
  rw [htranslate]
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi hSinvdet
  have happly := congrArg (fun μ : Measure (Fin n → ℝ) => μ (quadBall n)) hmap
  change (Measure.map (Matrix.toLin' S⁻¹) volume) (quadBall n) =
    (ENNReal.ofReal |S⁻¹.det⁻¹| • volume) (quadBall n) at happly
  rw [Measure.map_apply (by fun_prop) (measurable_quadBall n), Measure.smul_apply] at happly
  simp only [smul_eq_mul] at happly
  change volume ((fun x => S⁻¹.mulVec x) ⁻¹' quadBall n) =
    ENNReal.ofReal |S⁻¹.det⁻¹| * volume (quadBall n) at happly
  rw [happly]
  congr 1
  rw [Matrix.det_nonsing_inv, hSdet]
  simp [Ring.inverse_eq_inv, abs_of_pos (Real.sqrt_pos.2 hdetpos)]

theorem det_one_sub_vecMulVec {n : ℕ} (u v : Fin n → ℝ) (c : ℝ) :
    det (1 - c • vecMulVec u v) = 1 - c * (v ⬝ᵥ u) := by
  classical
  have hmat :
      -(c • vecMulVec u v) =
        Matrix.replicateCol Unit (-(c • u)) * Matrix.replicateRow Unit v := by
    ext i j
    simp [Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow, vecMulVec]
    ring
  rw [sub_eq_add_neg, hmat, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  have hsum : (∑ x, v x * -(c * u x)) = -c * (∑ x, v x * u x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hsum]
  ring

theorem ellipsoid_update_det {n : ℕ} (hn : 2 ≤ n)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    (ellipsoidUpdateMatrix D a).det =
      (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ n) *
        (((n : ℝ) - 1) / ((n : ℝ) + 1)) * D.det := by
  classical
  let q : ℝ := a ⬝ᵥ D.mulVec a
  let c : ℝ := 2 / ((n : ℝ) + 1)
  have hq : 0 < q := by
    dsimp [q]
    exact hD.dotProduct_mulVec_pos ha
  have hsymm : Dᵀ = D := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using hD.isHermitian.eq
  have hrank : vecMulVec a a * D = vecMulVec a (D.mulVec a) := by
    ext i j
    simp only [Matrix.mul_apply, vecMulVec, Matrix.of_apply, mulVec, dotProduct]
    have hentry (x : Fin n) : D x j = D j x := by
      have := congrFun (congrFun hsymm j) x
      simpa using this
    simp_rw [hentry]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  have hfactor :
      D - c • q⁻¹ • (D * vecMulVec a a * D) =
        D * (1 - (c * q⁻¹) • vecMulVec a (D.mulVec a)) := by
    rw [smul_smul]
    rw [Matrix.mul_assoc, hrank]
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  unfold ellipsoidUpdateMatrix
  change det (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
      (D - c • q⁻¹ • (D * vecMulVec a a * D))) = _
  rw [hfactor, Matrix.det_smul, Matrix.det_mul,
    det_one_sub_vecMulVec]
  simp only [Fintype.card_fin]
  have hdot : D.mulVec a ⬝ᵥ a = q := by
    dsimp [q]
    rw [dotProduct_comm]
  rw [hdot]
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  dsimp [c]
  field_simp [hq0]
  ring

theorem ellipsoid_ratio_lt_exp {n : ℕ} (hn : 2 ≤ n) :
    Real.sqrt
        ((((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ n) *
          (((n : ℝ) - 1) / ((n : ℝ) + 1))) <
      Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1))) := by
  let N : ℝ := n
  let α : ℝ := N ^ 2 / (N ^ 2 - 1)
  let r : ℝ := (N - 1) / (N + 1)
  let A : ℝ := α ^ n * r
  have hN : (2 : ℝ) ≤ N := by
    dsimp [N]
    exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hNm1 : 0 < N - 1 := by linarith
  have hNp1 : 0 < N + 1 := by linarith
  have hNsq : 0 < N ^ 2 - 1 := by nlinarith [sq_nonneg (N - 2)]
  have hα : 0 < α := by dsimp [α]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hαne : α ≠ 1 := by
    dsimp [α]
    intro h
    field_simp at h
    nlinarith
  have hαsub : α - 1 = 1 / (N ^ 2 - 1) := by
    dsimp [α]
    field_simp
    ring
  have hlogα : Real.log α < 1 / (N ^ 2 - 1) := by
    rw [← hαsub]
    exact Real.log_lt_sub_one_of_pos hα hαne
  let x : ℝ := 1 / N
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x < 1 := by dsimp [x]; rw [div_lt_one hN0]; linarith
  have hseries := Real.sum_range_le_log_div hx0 hx1 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_one,
    Nat.reduceMul, Nat.reduceAdd, pow_one, div_one] at hseries
  have hlogbig : 2 * x ≤ Real.log ((1 + x) / (1 - x)) := by
    nlinarith
  have hratio_inv : r = ((1 + x) / (1 - x))⁻¹ := by
    dsimp [r, x]
    field_simp
  have hlogr : Real.log r ≤ -2 / N := by
    rw [hratio_inv, Real.log_inv]
    dsimp [x] at hlogbig ⊢
    have htwodiv : 2 * (1 / N) = 2 / N := by ring
    rw [htwodiv] at hlogbig
    calc
      -Real.log ((1 + 1 / N) / (1 - 1 / N)) ≤ -(2 / N) := neg_le_neg hlogbig
      _ = -2 / N := by ring
  have hlogAeq : Real.log A = N * Real.log α + Real.log r := by
    dsimp [A]
    rw [Real.log_mul (pow_ne_zero _ hα.ne') hr.ne', Real.log_pow]
  have hfirst : N * Real.log α < N / (N ^ 2 - 1) := by
    have := mul_lt_mul_of_pos_left hlogα hN0
    convert this using 1 <;> ring
  have hrough : Real.log A < N / (N ^ 2 - 1) - 2 / N := by
    rw [hlogAeq]
    calc
      N * Real.log α + Real.log r < N / (N ^ 2 - 1) + Real.log r :=
        add_lt_add_of_lt_of_le hfirst (le_refl _)
      _ ≤ N / (N ^ 2 - 1) + (-2 / N) := add_le_add (le_refl _) hlogr
      _ = N / (N ^ 2 - 1) - 2 / N := by ring
  have hratbound : N / (N ^ 2 - 1) - 2 / N ≤ -1 / (N + 1) := by
    field_simp [ne_of_gt hN0, ne_of_gt hNsq, ne_of_gt hNp1]
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) (by linarith : 0 ≤ N + 1)]
  have hlogA : Real.log A < -1 / (N + 1) := hrough.trans_le hratbound
  have hAexp : A < Real.exp (-1 / (N + 1)) :=
    (Real.log_lt_iff_lt_exp hA).mp hlogA
  change Real.sqrt A < Real.exp (-(1 : ℝ) / (2 * (N + 1)))
  rw [Real.sqrt_lt' (Real.exp_pos _)]
  rw [pow_two, ← Real.exp_add]
  have heq :
      -(1 : ℝ) / (2 * (N + 1)) + -(1 : ℝ) / (2 * (N + 1)) =
        -1 / (N + 1) := by
    field_simp [ne_of_gt hNp1]
    ring
  rw [heq]
  exact hAexp

theorem solution {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    volume (ellipsoid (ellipsoidUpdateCenter z D a)
        (ellipsoidUpdateMatrix D a)) <
      ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1)))) *
        volume (ellipsoid z D) := by
  classical
  let R : ℝ :=
    (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ n) *
      (((n : ℝ) - 1) / ((n : ℝ) + 1))
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hRpos : 0 < R := by
    have hn0R : 0 < (n : ℝ) := by linarith
    have hden : 0 < (n : ℝ) ^ 2 - 1 := by
      nlinarith [sq_nonneg ((n : ℝ) - 2)]
    dsimp [R]
    exact mul_pos (pow_pos (div_pos (sq_pos_of_pos hn0R) hden) _)
      (div_pos (by linarith) (by linarith))
  have hDbar : (ellipsoidUpdateMatrix D a).PosDef :=
    LinearOptimization.ellipsoid_update_matrix_posDef hn D hD a ha
  rw [ellipsoid_volume_formula _ _ hDbar,
    ellipsoid_volume_formula z D hD]
  rw [ellipsoid_update_det hn D hD a ha]
  change ENNReal.ofReal (Real.sqrt (R * D.det)) * volume (quadBall n) <
    ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1)))) *
      (ENNReal.ofReal (Real.sqrt D.det) * volume (quadBall n))
  rw [Real.sqrt_mul hRpos.le]
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg R)]
  have hcoef :
      ENNReal.ofReal (Real.sqrt R) <
        ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1)))) :=
    (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).2
      (by simpa [R] using ellipsoid_ratio_lt_exp hn)
  have hn0 : 0 < n := lt_of_lt_of_le (by omega : 0 < 2) hn
  let i0 : Fin n := ⟨0, hn0⟩
  letI : Nonempty (Fin n) := ⟨i0⟩
  let K := ENNReal.ofReal (Real.sqrt D.det) * volume (quadBall n)
  have hKpos : 0 < K := by
    dsimp [K]
    exact ENNReal.mul_pos_iff.2
      ⟨ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hD.det_pos), volume_quadBall_pos⟩
  have hKtop : K ≠ ⊤ := by
    dsimp [K]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt volume_quadBall_lt_top)
  calc
    ENNReal.ofReal (Real.sqrt R) * ENNReal.ofReal (Real.sqrt D.det) *
          volume (quadBall n) = K * ENNReal.ofReal (Real.sqrt R) := by
            dsimp [K]; ac_rfl
    _ < K * ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1)))) :=
      ENNReal.mul_lt_mul_right hKpos.ne' hKtop hcoef
    _ = ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1)))) *
          (ENNReal.ofReal (Real.sqrt D.det) * volume (quadBall n)) := by
            dsimp [K]; ac_rfl
