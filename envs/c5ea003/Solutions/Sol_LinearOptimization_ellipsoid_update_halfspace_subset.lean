-- Prove2me | solution 1 for LinearOptimization.ellipsoid_update_halfspace_subset
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-09T17:20:12.738036+00:00
-- url     : https://prove2.me/submissions/f9923a82-a99d-47a0-b8f5-a5c4c4d76229

import Definitions.Def_LinearOptimization_EllipsoidMethod
import Mathlib.Tactic

open Matrix LinearOptimization

theorem test_update_inverse {n : ℕ} (hn : 2 ≤ n)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    (ellipsoidUpdateMatrix D a)⁻¹ =
      ((((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2) •
        (D⁻¹ + ((2 : ℝ) / ((n : ℝ) - 1)) •
          (a ⬝ᵥ D.mulVec a)⁻¹ • vecMulVec a a)) := by
  classical
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by nlinarith
  have hden : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith [sq_nonneg ((n : ℝ) - 2)]
  have hq : 0 < a ⬝ᵥ D.mulVec a := hD.dotProduct_mulVec_pos ha
  have hq0 : a ⬝ᵥ D.mulVec a ≠ 0 := ne_of_gt hq
  have hDunit : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit
  have hrank :
      vecMulVec a a * D * vecMulVec a a =
        (a ⬝ᵥ D.mulVec a) • vecMulVec a a := by
    ext i j
    simp only [Matrix.mul_apply, vecMulVec, Matrix.of_apply, dotProduct, mulVec,
      smul_apply, smul_eq_mul]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  apply Matrix.inv_eq_left_inv
  unfold ellipsoidUpdateMatrix
  simp only [Matrix.smul_mul, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_sub]
  simp_rw [← Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul D hDunit]
  simp only [Matrix.one_mul]
  rw [hrank]
  simp only [Matrix.smul_mul]
  ext i j
  simp only [smul_apply, sub_apply, add_apply, one_apply, smul_eq_mul]
  field_simp [hn0, hn1, hden, hq0]
  ring_nf

theorem solution {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    ellipsoid z D ∩ {x | a ⬝ᵥ z ≤ a ⬝ᵥ x} ⊆
      ellipsoid (ellipsoidUpdateCenter z D a) (ellipsoidUpdateMatrix D a) := by
  classical
  rintro x ⟨hxE, hxH⟩
  unfold ellipsoid at hxE ⊢
  let y : Fin n → ℝ := x - z
  let u : Fin n → ℝ := D.mulVec a
  let q : ℝ := a ⬝ᵥ D.mulVec a
  let p : ℝ := a ⬝ᵥ y
  let s : ℝ := y ⬝ᵥ D⁻¹.mulVec y
  let c : ℝ := 1 / ((n : ℝ) + 1)
  let δ : ℝ := 2 / ((n : ℝ) - 1)
  let β : ℝ := ((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2
  let r : ℝ := Real.sqrt q
  change s ≤ 1 at hxE
  change a ⬝ᵥ z ≤ a ⬝ᵥ x at hxH
  have hp : 0 ≤ p := by
    dsimp [p, y]
    rw [dotProduct_sub]
    linarith
  have hq : 0 < q := by
    dsimp [q]
    exact hD.dotProduct_mulVec_pos ha
  have hr0 : 0 ≤ r := by simp [r]
  have hr : 0 < r := Real.sqrt_pos.2 hq
  have hr2 : r ^ 2 = q := by simp [r, Real.sq_sqrt hq.le]
  have hDunit : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit
  have hu : u ≠ 0 := by
    intro hu0
    have h := congrArg (D⁻¹.mulVec) hu0
    dsimp [u] at h
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul D hDunit] at h
    have : a = 0 := by simpa using h
    exact ha this
  have hDinvT : D⁻¹ᵀ = D⁻¹ := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using hD.inv.isHermitian.eq
  have hsymmInv (v w : Fin n → ℝ) :
      v ⬝ᵥ D⁻¹.mulVec w = w ⬝ᵥ D⁻¹.mulVec v := by
    have hv : v ᵥ* D⁻¹ = D⁻¹ᵀ.mulVec v := by
      simpa using Matrix.vecMul_transpose D⁻¹ᵀ v
    calc
      v ⬝ᵥ D⁻¹.mulVec w = v ᵥ* D⁻¹ ⬝ᵥ w := Matrix.dotProduct_mulVec _ _ _
      _ = D⁻¹ᵀ.mulVec v ⬝ᵥ w := by rw [hv]
      _ = D⁻¹.mulVec v ⬝ᵥ w := by rw [hDinvT]
      _ = w ⬝ᵥ D⁻¹.mulVec v := dotProduct_comm _ _
  have hinvDmul (v : Fin n → ℝ) : D⁻¹.mulVec (D.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul D hDunit]
    simp
  have hqu : u ⬝ᵥ D⁻¹.mulVec u = q := by
    rw [hsymmInv]
    simp [u, q, hinvDmul, dotProduct_comm]
  have hpu : u ⬝ᵥ D⁻¹.mulVec y = p := by
    rw [hsymmInv]
    simp [u, p, hinvDmul, dotProduct_comm]
  have hcs : p ^ 2 ≤ q * s := by
    have hnonneg := hD.inv.posSemidef.dotProduct_mulVec_nonneg
      (y - (p / q) • u)
    simp only [star_trivial, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
      smul_dotProduct, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hnonneg
    rw [hpu, hsymmInv y u, hpu, hqu] at hnonneg
    change 0 ≤ s - (p / q) * p - (p / q) * (p - (p / q) * q) at hnonneg
    have hmul := mul_nonneg hq.le hnonneg
    field_simp [ne_of_gt hq] at hmul
    nlinarith
  let t : ℝ := p / r
  have ht0 : 0 ≤ t := div_nonneg hp hr0
  have ht1 : t ≤ 1 := by
    have hp2q : p ^ 2 ≤ q := by nlinarith [mul_le_mul_of_nonneg_left hxE hq.le]
    dsimp [t]
    rw [div_le_one hr]
    nlinarith
  have hyb :
      x - ellipsoidUpdateCenter z D a = y - (c / r) • u := by
    ext i
    simp only [ellipsoidUpdateCenter, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    dsimp [y, u, c, r, q]
    field_simp [ne_of_gt hr]
    ring
  change (x - ellipsoidUpdateCenter z D a) ⬝ᵥ
      (ellipsoidUpdateMatrix D a)⁻¹.mulVec
        (x - ellipsoidUpdateCenter z D a) ≤ 1
  rw [test_update_inverse hn D hD a ha, hyb]
  change (y - (c / r) • u) ⬝ᵥ
      (β • (D⁻¹ + δ • q⁻¹ • vecMulVec a a)).mulVec
        (y - (c / r) • u) ≤ 1
  have hay : a ⬝ᵥ y = p := rfl
  have hau : a ⬝ᵥ u = q := rfl
  have hya : y ⬝ᵥ a = p := (dotProduct_comm y a).trans hay
  have hua : u ⬝ᵥ a = q := (dotProduct_comm u a).trans hau
  have hcalc :
      (y - (c / r) • u) ⬝ᵥ
          (β • (D⁻¹ + δ • q⁻¹ • vecMulVec a a)).mulVec
            (y - (c / r) • u) =
        β * (s + δ * t ^ 2 - (2 / ((n : ℝ) - 1)) * t +
          1 / ((n : ℝ) ^ 2 - 1)) := by
    simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.mulVec_sub,
      Matrix.mulVec_smul, Matrix.vecMulVec_mulVec, sub_dotProduct,
      smul_dotProduct, dotProduct_sub, dotProduct_smul, add_dotProduct,
      dotProduct_add, op_smul_eq_smul, smul_eq_mul]
    rw [hpu, hsymmInv y u, hpu, hqu]
    simp only [hay, hau, hya, hua]
    have hnR' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hnm1 : (n : ℝ) - 1 ≠ 0 := by nlinarith
    have hnp1 : (n : ℝ) + 1 ≠ 0 := by nlinarith
    have hnsq1 : (n : ℝ) ^ 2 - 1 ≠ 0 := by
      nlinarith [sq_nonneg ((n : ℝ) - 2)]
    dsimp [β, δ, c, t, s]
    rw [← hr2]
    field_simp [ne_of_gt hq, ne_of_gt hr, hnm1, hnp1, hnsq1]
    ring_nf
  rw [hcalc]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  have hdenpos : 0 < (n : ℝ) ^ 2 - 1 := by
    nlinarith [sq_nonneg ((n : ℝ) - 2)]
  have hβ : 0 < β := by
    dsimp [β]
    positivity
  have htquad : t ^ 2 - t ≤ 0 := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  dsimp [δ]
  have hinside :
      s + (2 / ((n : ℝ) - 1)) * t ^ 2 -
          (2 / ((n : ℝ) - 1)) * t + 1 / ((n : ℝ) ^ 2 - 1) ≤
        1 + 1 / ((n : ℝ) ^ 2 - 1) := by
    have hcoef : 0 ≤ (2 : ℝ) / ((n : ℝ) - 1) := by positivity
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hcoef htquad]
  have hβid : β * (1 + 1 / ((n : ℝ) ^ 2 - 1)) = 1 := by
    dsimp [β]
    field_simp [ne_of_gt hn0, ne_of_gt hdenpos]
    ring_nf
  calc
    β * (s + 2 / (↑n - 1) * t ^ 2 - 2 / (↑n - 1) * t +
      1 / (↑n ^ 2 - 1))
        ≤ β * (1 + 1 / (↑n ^ 2 - 1)) :=
          mul_le_mul_of_nonneg_left hinside hβ.le
    _ = 1 := hβid
