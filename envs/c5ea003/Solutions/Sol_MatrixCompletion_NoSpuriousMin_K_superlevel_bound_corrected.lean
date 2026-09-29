-- Prove2me | solution 1 for MatrixCompletion.NoSpuriousMin.K_superlevel_bound_corrected
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-14T19:02:45.455513+00:00
-- url     : https://prove2.me/submissions/7740ffe7-fce0-4652-946d-820af6300247

import Theorems.Thm_MatrixCompletion_NoSpuriousMin_K_decomposition
import Theorems.Thm_MatrixCompletion_NoSpuriousMin_perturbation_terms_bound_corrected
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_MCNoSpuriousMinModel
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

open Matrix Finset MatrixCompletion.NoSpuriousMin

namespace KSuperAux

variable {m n : ℕ}

lemma conjT_real {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) : Aᴴ = Aᵀ := by
  ext i j; simp [Matrix.conjTranspose_apply]

lemma frobSq_nonneg (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ frobSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma frobNorm_sq (A : Matrix (Fin m) (Fin n) ℝ) : frobNorm A ^ 2 = frobSq A :=
  Real.sq_sqrt (frobSq_nonneg A)

lemma frobNorm_nonneg (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ frobNorm A := Real.sqrt_nonneg _

lemma frobSq_eq_innerM (A : Matrix (Fin m) (Fin n) ℝ) : frobSq A = innerM A A := by
  simp only [frobSq, innerM, sq]

/-- The Frobenius pairing as a trace. -/
lemma innerM_eq_trace (A B : Matrix (Fin m) (Fin n) ℝ) : innerM A B = (Aᵀ * B).trace := by
  simp only [innerM, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

lemma frobSq_eq_trace (A : Matrix (Fin m) (Fin n) ℝ) : frobSq A = (Aᵀ * A).trace := by
  rw [frobSq_eq_innerM, innerM_eq_trace]

lemma innerM_comm (A B : Matrix (Fin m) (Fin n) ℝ) : innerM A B = innerM B A := by
  simp only [innerM]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

lemma innerM_add_left (A B C : Matrix (Fin m) (Fin n) ℝ) :
    innerM (A + B) C = innerM A C + innerM B C := by
  simp only [innerM, Matrix.add_apply, add_mul, ← Finset.sum_add_distrib]

lemma innerM_add_right (A B C : Matrix (Fin m) (Fin n) ℝ) :
    innerM A (B + C) = innerM A B + innerM A C := by
  simp only [innerM, Matrix.add_apply, mul_add, ← Finset.sum_add_distrib]

/-- Cauchy–Schwarz for the Frobenius pairing. -/
lemma abs_innerM_le (A B : Matrix (Fin m) (Fin n) ℝ) :
    |innerM A B| ≤ frobNorm A * frobNorm B := by
  have hsq : innerM A B ^ 2 ≤ frobSq A * frobSq B := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m × Fin n))
      (fun q => A q.1 q.2) (fun q => B q.1 q.2)
    simpa [innerM, frobSq, Fintype.sum_prod_type] using h
  have hy : 0 ≤ frobNorm A * frobNorm B := mul_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _)
  have h2 : |innerM A B| ^ 2 ≤ (frobNorm A * frobNorm B) ^ 2 := by
    rw [sq_abs, mul_pow, frobNorm_sq, frobNorm_sq]; exact hsq
  nlinarith [abs_nonneg (innerM A B), h2, hy]

lemma frobSq_mul_transpose_comm {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) :
    frobSq (A * Aᵀ) = frobSq (Aᵀ * A) := by
  rw [frobSq_eq_trace, frobSq_eq_trace]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp [Matrix.mul_assoc]

/-- `‖P_Ω A‖_F² = D_{Ω,t}(A,A) + t‖A‖_F²`. -/
lemma frobSq_projSet {k : ℕ} (Ω : Finset (Fin k × Fin k)) (t : ℝ)
    (A : Matrix (Fin k) (Fin k) ℝ) :
    frobSq (projSet Ω A) = sampDev Ω t A A + t * frobSq A := by
  simp only [sampDev, frobSq, innerM, sq]
  ring

end KSuperAux

open KSuperAux

set_option maxHeartbeats 1000000 in
theorem solution {d r : ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r)
    (Z X U : Matrix (Fin d) (Fin r) ℝ) (Ω : Finset (Fin d × Fin d))
    (p μ κ lam α : ℝ)
    (hμ : 1 ≤ μ) (hκ : 1 ≤ κ) (hcond : sigmaMax Z ≤ κ * sigmaMin Z)
    (hσ : 0 < sigmaMin Z)
    (hinc : Incoherent μ Z) (hZnorm : frobSq Z = (r : ℝ))
    (hα1 : 100 * twoInftyNorm Z ≤ α) (hα2 : α ≤ 200 * twoInftyNorm Z)
    (hlam1 : 100 * sampDevNorm Ω p ≤ lam) (hlam2 : lam ≤ 200 * sampDevNorm Ω p)
    (hp : SampleCondition d r p μ κ)
    (hpC : 10 ^ 28 * μ ^ 4 * κ ^ 4 * (r : ℝ) ^ 2 * (1 + Real.log d) / d ≤ p)
    (hgood : GoodSample Z Ω p)
    (hU : U * Uᵀ = Z * Zᵀ) (hpsd : (Xᵀ * U).PosSemidef) :
    Kfun Z Ω lam α X U ≤
      p * (-(198 / 100) * frobSq ((X - U)ᵀ * (X - U))
        + (602 / 100) * frobNorm ((X - U)ᵀ * (X - U)) * frobNorm ((X - U)ᵀ * U)
        - 6 * frobSq ((X - U)ᵀ * U)) := by
  classical
  -- `p` is positive.
  have hp0 : 0 < p := by
    have hd1 : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
    have hlog : 0 < Real.log (d : ℝ) := Real.log_pos hd1
    have hμ0 : (0 : ℝ) < μ := by linarith
    have hκ0 : (0 : ℝ) < κ := by linarith
    have hrpos : (0 : ℝ) < (r : ℝ) := by
      have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      linarith
    have hnum : (0 : ℝ) < 10 ^ 10 * μ ^ 4 * κ ^ 4 * (r : ℝ) ^ 2 * Real.log (d : ℝ) :=
      mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hμ0 4)) (pow_pos hκ0 4))
        (pow_pos hrpos 2)) hlog
    have := div_pos hnum hdpos
    linarith [hp.1]
  set Δ : Matrix (Fin d) (Fin r) ℝ := X - U with hΔ
  -- `Δᵀ U` is symmetric, because `Xᵀ U` is.
  have hSsplit : Δᵀ * U = Xᵀ * U - Uᵀ * U := by
    rw [hΔ, Matrix.transpose_sub, Matrix.sub_mul]
  have hXUeq : Xᵀ * U = Uᵀ * U + Δᵀ * U := by rw [hSsplit]; abel
  have hXUsymm : (Xᵀ * U)ᵀ = Xᵀ * U := by rw [← conjT_real]; exact hpsd.isHermitian
  have hUD : Uᵀ * Δ = Δᵀ * U := by
    have h : (Δᵀ * U)ᵀ = Δᵀ * U := by
      rw [hSsplit, Matrix.transpose_sub, hXUsymm, Matrix.transpose_mul, Matrix.transpose_transpose]
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose] at h
  set a := frobNorm (Δᵀ * Δ) with hadef
  set b := frobNorm (Δᵀ * U) with hbdef
  set c := frobSq (U * Δᵀ) with hcdef
  set t := innerM (Δᵀ * U) (Δᵀ * Δ) with htdef
  have ha2 : a ^ 2 = frobSq (Δᵀ * Δ) := frobNorm_sq _
  have hb2 : b ^ 2 = frobSq (Δᵀ * U) := frobNorm_sq _
  have hanneg : 0 ≤ a := frobNorm_nonneg _
  have hbnneg : 0 ≤ b := frobNorm_nonneg _
  -- Trace identities among the six pairings that appear in `‖E‖_F²`.
  have hPP : innerM (U * Δᵀ) (U * Δᵀ) = c := (frobSq_eq_innerM _).symm
  have hQQ : innerM (Δ * Uᵀ) (Δ * Uᵀ) = c := by
    rw [← frobSq_eq_innerM, hcdef, frobSq_eq_trace, frobSq_eq_trace]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
  have hRR : innerM (Δ * Δᵀ) (Δ * Δᵀ) = a ^ 2 := by
    rw [← frobSq_eq_innerM, ha2]
    exact frobSq_mul_transpose_comm Δ
  have hPQ : innerM (U * Δᵀ) (Δ * Uᵀ) = b ^ 2 := by
    rw [hb2, innerM_eq_trace, frobSq_eq_trace]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm, ← hUD]
    simp [Matrix.mul_assoc]
  have hQP : innerM (Δ * Uᵀ) (U * Δᵀ) = b ^ 2 := by rw [innerM_comm]; exact hPQ
  have hPR : innerM (U * Δᵀ) (Δ * Δᵀ) = t := by
    rw [htdef, innerM_eq_trace, innerM_eq_trace]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
  have hRP : innerM (Δ * Δᵀ) (U * Δᵀ) = t := by rw [innerM_comm]; exact hPR
  have hQR : innerM (Δ * Uᵀ) (Δ * Δᵀ) = t := by
    rw [htdef, innerM_eq_trace, innerM_eq_trace, ← hUD]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
  have hRQ : innerM (Δ * Δᵀ) (Δ * Uᵀ) = t := by rw [innerM_comm]; exact hQR
  have hI6 : c = innerM (Uᵀ * U) (Δᵀ * Δ) := by
    rw [hcdef, frobSq_eq_trace, innerM_eq_trace]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
  -- The residual splits, and its squared norm expands.
  have hE : X * Xᵀ - U * Uᵀ = U * Δᵀ + Δ * Uᵀ + Δ * Δᵀ := by
    rw [hΔ]
    simp only [Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul]
    abel
  have hEsq : frobSq (X * Xᵀ - U * Uᵀ) = 2 * c + 2 * b ^ 2 + 4 * t + a ^ 2 := by
    rw [hE, frobSq_eq_innerM]
    simp only [innerM_add_left, innerM_add_right, hPP, hQQ, hRR, hPQ, hQP, hPR, hRP, hQR, hRQ]
    ring
  -- The two lower bounds on `t` that make the constants exact.
  have htlow1 : -(a * b) ≤ t := by
    have habs : |t| ≤ b * a := by rw [htdef]; exact abs_innerM_le _ _
    have := (abs_le.mp habs).1
    linarith [this]
  have htlow2 : -c ≤ t := by
    have hpsdconj := hpsd.mul_mul_conjTranspose_same Δ
    rw [conjT_real] at hpsdconj
    have htrnn : 0 ≤ (Δ * (Xᵀ * U) * Δᵀ).trace := hpsdconj.trace_nonneg
    have htr : (Δ * (Xᵀ * U) * Δᵀ).trace = ((Xᵀ * U) * (Δᵀ * Δ)).trace := by
      rw [Matrix.trace_mul_comm (Δ * (Xᵀ * U)) Δᵀ, ← Matrix.mul_assoc,
        Matrix.trace_mul_comm (Δᵀ * Δ) (Xᵀ * U)]
    have hsplit2 : ((Xᵀ * U) * (Δᵀ * Δ)).trace = c + t := by
      rw [hXUeq, Matrix.add_mul, Matrix.trace_add]
      congr 1
      · rw [hI6, innerM_eq_trace, Matrix.transpose_mul, Matrix.transpose_transpose]
      · rw [htdef, innerM_eq_trace, Matrix.transpose_mul, Matrix.transpose_transpose, hUD]
    rw [htr, hsplit2] at htrnn
    linarith
  -- The two imported milestones.
  have hK := MatrixCompletion.NoSpuriousMin.K_decomposition Z X U Ω lam α hgood.symm hU
  have hpert := MatrixCompletion.NoSpuriousMin.perturbation_terms_bound_corrected hd hr
    Z X U Ω p μ κ lam α
    hμ hκ hcond hσ hinc hZnorm hα1 hα2 hlam1 hlam2 hp hpC hgood hU hpsd
  have hA := frobSq_projSet Ω p (Δ * Δᵀ)
  have hB := frobSq_projSet Ω p (X * Xᵀ - U * Uᵀ)
  have hRRfrob : frobSq (Δ * Δᵀ) = a ^ 2 := by rw [ha2]; exact frobSq_mul_transpose_comm Δ
  have hKval : Kfun Z Ω lam α X U
      = (sampDev Ω p (Δ * Δᵀ) (Δ * Δᵀ)
          - 3 * sampDev Ω p (X * Xᵀ - U * Uᵀ) (X * Xᵀ - U * Uᵀ)
          + lam * (regHessQF α X Δ - 4 * innerM (regGrad α X) Δ))
        + p * (a ^ 2 - 3 * (2 * c + 2 * b ^ 2 + 4 * t + a ^ 2)) := by
    rw [hK, hA, hB, hRRfrob, hEsq]; ring
  rw [← ha2] at hpert
  rw [hKval, ← ha2, ← hb2]
  have key : (a ^ 2 + c) / 50
      + (a ^ 2 - 3 * (2 * c + 2 * b ^ 2 + 4 * t + a ^ 2))
      ≤ -(198 / 100) * a ^ 2 + (602 / 100) * a * b - 6 * b ^ 2 := by
    linarith
  nlinarith [mul_le_mul_of_nonneg_left key hp0.le, hpert, hp0]
