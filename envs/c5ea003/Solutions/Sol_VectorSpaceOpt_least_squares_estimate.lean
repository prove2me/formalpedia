-- Prove2me | solution 1 for VectorSpaceOpt.least_squares_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T13:47:55.615119+00:00
-- url     : https://prove2.me/submissions/6d47b4c6-d43a-4bf9-a6ea-fab81869747c

import Mathlib
open Matrix


theorem solution {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ)
    (hW : LinearIndependent ℝ (fun j : Fin n => fun i : Fin m => W i j))
    (y : Fin m → ℝ) (βls : Fin n → ℝ)
    (hβls : βls = (Wᵀ * W)⁻¹.mulVec (Wᵀ.mulVec y)) :
    (∀ β : Fin n → ℝ,
      ∑ i, (y i - W.mulVec βls i) ^ 2 ≤ ∑ i, (y i - W.mulVec β i) ^ 2) ∧
    (∀ β : Fin n → ℝ,
      (∀ β' : Fin n → ℝ,
        ∑ i, (y i - W.mulVec β i) ^ 2 ≤ ∑ i, (y i - W.mulVec β' i) ^ 2) →
      β = βls) := by
  classical
  have hinj : ∀ x : Fin n → ℝ, W.mulVec x = 0 → x = 0 := by
    intro x hx
    funext j
    refine (Fintype.linearIndependent_iff.1 hW) x ?_ j
    funext i
    have hi : W.mulVec x i = 0 := congrFun hx i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hi]
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hquad : ∀ x : Fin n → ℝ,
      x ⬝ᵥ ((Wᵀ * W).mulVec x) = (W.mulVec x) ⬝ᵥ (W.mulVec x) := by
    intro x
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.mulVec_transpose,
      Matrix.transpose_transpose]
  have hzero_of_dot : ∀ v : Fin m → ℝ, v ⬝ᵥ v = 0 → v = 0 := by
    intro v hv
    funext i
    have hs : ∑ i, v i * v i = 0 := hv
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_self_nonneg (v i))).1 hs i (Finset.mem_univ i)
    simpa [mul_self_eq_zero] using this
  have hGinj : Function.Injective (Wᵀ * W).mulVec := by
    intro a b hab
    have h0 : (Wᵀ * W).mulVec (a - b) = 0 := by
      rw [Matrix.mulVec_sub, hab, sub_self]
    have h1 : (W.mulVec (a - b)) ⬝ᵥ (W.mulVec (a - b)) = 0 := by
      rw [← hquad, h0, dotProduct_zero]
    exact sub_eq_zero.1 (hinj _ (hzero_of_dot _ h1))
  have hGu : IsUnit (Wᵀ * W) := Matrix.mulVec_injective_iff_isUnit.1 hGinj
  have hGdet : IsUnit (Wᵀ * W).det := (Matrix.isUnit_iff_isUnit_det _).1 hGu
  have hnormal : Wᵀ.mulVec (y - W.mulVec βls) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hβls, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hGdet, Matrix.one_mulVec, sub_self]
  have horth : ∀ δ : Fin n → ℝ, (y - W.mulVec βls) ⬝ᵥ (W.mulVec δ) = 0 := by
    intro δ
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hnormal, zero_dotProduct]
  have hsum_dot : ∀ β : Fin n → ℝ,
      ∑ i, (y i - W.mulVec β i) ^ 2 = (y - W.mulVec β) ⬝ᵥ (y - W.mulVec β) := by
    intro β
    simp only [dotProduct, Pi.sub_apply, pow_two]
  have hexp : ∀ β : Fin n → ℝ,
      (y - W.mulVec β) ⬝ᵥ (y - W.mulVec β)
        = (y - W.mulVec βls) ⬝ᵥ (y - W.mulVec βls)
          + (W.mulVec (βls - β)) ⬝ᵥ (W.mulVec (βls - β)) := by
    intro β
    have hsplit : y - W.mulVec β = (y - W.mulVec βls) + W.mulVec (βls - β) := by
      rw [Matrix.mulVec_sub]; abel
    rw [hsplit, add_dotProduct, dotProduct_add, dotProduct_add, horth (βls - β)]
    have hcomm : (W.mulVec (βls - β)) ⬝ᵥ (y - W.mulVec βls)
        = (y - W.mulVec βls) ⬝ᵥ (W.mulVec (βls - β)) := dotProduct_comm _ _
    rw [hcomm, horth (βls - β)]
    ring
  have hnn : ∀ δ : Fin n → ℝ, 0 ≤ (W.mulVec δ) ⬝ᵥ (W.mulVec δ) := by
    intro δ
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  constructor
  · intro β
    rw [hsum_dot βls, hsum_dot β, hexp β]
    linarith [hnn (βls - β)]
  · intro β hβ
    have h1 := hβ βls
    rw [hsum_dot β, hsum_dot βls, hexp β] at h1
    have h2 : (W.mulVec (βls - β)) ⬝ᵥ (W.mulVec (βls - β)) = 0 :=
      le_antisymm (by linarith) (hnn (βls - β))
    have h3 := hinj _ (hzero_of_dot _ h2)
    exact (sub_eq_zero.1 h3).symm
