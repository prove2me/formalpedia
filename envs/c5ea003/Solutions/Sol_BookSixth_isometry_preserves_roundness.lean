-- Prove2me | solution 1 for BookSixth.isometry_preserves_roundness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T01:28:56.47098+00:00
-- url     : https://prove2.me/submissions/14e315c3-9a3c-4b86-953d-1b4de6d4a6a6

import Mathlib
import Definitions.Def_BookSixth
open BookSixth

theorem solution (C : Set Space3)
    (A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) (b : Space3) (a : ℝ)
    (hA : ∀ x : Space3, ‖A x‖ = ‖x‖) (ha : 0 < a) (hC : RoundCircle C) :
    RoundCircle ((fun x : Space3 => a • (A x) + b) '' C) := by
  -- matrix coefficients
  set e : Fin 3 → Space3 := fun k => fun j => if k = j then (1 : ℝ) else 0 with he
  set M : Fin 3 → Fin 3 → ℝ := fun i k => A (e k) i with hM
  have hexp : ∀ x : Space3, ∀ i, A x i = ∑ k, x k * M i k := by
    intro x i
    conv_lhs => rw [pi_eq_sum_univ x]
    rw [map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hM, he]
  have hcoef : ∀ i k, |M i k| ≤ 1 := by
    intro i k
    have h1 : ‖A (e k) i‖ ≤ ‖A (e k)‖ := norm_le_pi_norm _ i
    rw [hA] at h1
    have h2 : ‖e k‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
      simp only [he]; split_ifs <;> simp
    have := h1.trans h2
    simpa [hM, Real.norm_eq_abs] using this
  -- row ℓ¹ bound
  have hrow : ∀ i, ∑ k, |M i k| ≤ 1 := by
    intro i
    set s : Space3 := fun k => if 0 ≤ M i k then 1 else -1 with hs
    have hsn : ‖s‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
      simp only [hs]; split_ifs <;> simp
    have h1 : ‖A s i‖ ≤ ‖A s‖ := norm_le_pi_norm _ i
    rw [hA] at h1
    have h3 : A s i = ∑ k, |M i k| := by
      rw [hexp]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hs]
      split_ifs with h
      · rw [abs_of_nonneg h]; ring
      · rw [abs_of_neg (lt_of_not_ge h)]; ring
    have := h1.trans hsn
    rw [h3, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  -- each column has a ±1 entry
  have hcol : ∀ k, ∃ i, |M i k| = 1 := by
    intro k
    by_contra hcon
    simp only [not_exists] at hcon
    have hlt : ‖A (e k)‖ < 1 := by
      refine (pi_norm_lt_iff zero_lt_one).2 fun i => ?_
      rw [Real.norm_eq_abs]
      exact lt_of_le_of_ne (hcoef i k) (hcon i)
    rw [hA] at hlt
    have : ‖e k‖ ≥ 1 := by
      have := norm_le_pi_norm (e k) k
      simpa [he] using this
    linarith
  choose σ hσ using hcol
  -- in row σ k, all other entries vanish
  have hzero : ∀ k l, l ≠ k → M (σ k) l = 0 := by
    intro k l hlk
    have hr := hrow (σ k)
    have hsplit : ∑ m, |M (σ k) m| = |M (σ k) k| + ∑ m ∈ Finset.univ.erase k, |M (σ k) m| := by
      rw [Finset.add_sum_erase _ (fun m => |M (σ k) m|) (Finset.mem_univ k)]
    rw [hsplit, hσ k] at hr
    have hnn : ∀ m ∈ Finset.univ.erase k, 0 ≤ |M (σ k) m| := fun _ _ => abs_nonneg _
    have hle : |M (σ k) l| ≤ ∑ m ∈ Finset.univ.erase k, |M (σ k) m| :=
      Finset.single_le_sum hnn (Finset.mem_erase.2 ⟨hlk, Finset.mem_univ l⟩)
    have : |M (σ k) l| ≤ 0 := by linarith
    exact abs_nonpos_iff.1 this
  have hinj : Function.Injective σ := by
    intro k l h
    by_contra hkl
    have h1 := hzero k l (Ne.symm hkl)
    rw [h] at h1
    have h2 := hσ l
    rw [h1, abs_zero] at h2
    exact zero_ne_one h2
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.1 hinj
  have hval : ∀ x : Space3, ∀ k, A x (σ k) = x k * M (σ k) k := by
    intro x k
    rw [hexp, Finset.sum_eq_single k]
    · intro l _ hlk; rw [hzero k l hlk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hsq : ∀ k, M (σ k) k * M (σ k) k = 1 := by
    intro k
    have := hσ k
    rw [← abs_mul_abs_self, this, one_mul]
  have hinner : ∀ x y : Space3, (∑ i, A x i * A y i) = ∑ i, x i * y i := by
    intro x y
    rw [← hbij.sum_comp (fun i => A x i * A y i)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hval, hval]
    calc x k * M (σ k) k * (y k * M (σ k) k) = x k * y k * (M (σ k) k * M (σ k) k) := by ring
      _ = x k * y k := by rw [hsq, mul_one]
  obtain ⟨c, u, v, r, hr, hu, hv, huv, rfl⟩ := hC
  refine ⟨a • A c + b, A u, A v, a * r, mul_pos ha hr, ?_, ?_, ?_, ?_⟩
  · rw [hinner]; exact hu
  · rw [hinner]; exact hv
  · rw [hinner]; exact huv
  · rw [← Set.range_comp]
    congr 1
    funext t
    simp only [Function.comp, map_add, map_smul]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
