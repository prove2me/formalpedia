-- Prove2me | solution 1 for lean_workbook_plus_30969
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:39:21.445346+00:00
-- url     : https://prove2.me/submissions/17bc5eaa-4a25-4afb-8310-59eaf425cacd

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.GroupTheory.Index
import Mathlib.Data.Fintype.Units
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Ring

open Matrix

private def specialLinearDetKernelEquiv (K : Type*) [Field K] :
    SpecialLinearGroup (Fin 2) K ≃
      (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ).ker where
  toFun M := ⟨M.toGL, by
    apply Units.ext
    exact M.property⟩
  invFun M := ⟨M.1.val, by
    exact congrArg Units.val M.property⟩
  left_inv M := by apply Subtype.ext; rfl
  right_inv M := by apply Subtype.ext; apply Units.ext; rfl

private theorem two_by_two_det_surjective (K : Type*) [Field K] :
    Function.Surjective (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ) := by
  intro u
  let M : Matrix (Fin 2) (Fin 2) K := !![(u : K), 0; 0, 1]
  have hm : IsUnit M.det := by simpa [M, det_fin_two] using u.isUnit
  refine ⟨GeneralLinearGroup.mk'' M hm, ?_⟩
  apply Units.ext
  simp [GeneralLinearGroup.det, M, det_fin_two]

theorem specialLinear_two_card (K : Type*) [Field K] [Fintype K] :
    Nat.card (SpecialLinearGroup (Fin 2) K) =
      Fintype.card K * (Fintype.card K ^ 2 - 1) := by
  let f : GL (Fin 2) K →* Kˣ := GeneralLinearGroup.det
  have hcard := f.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (two_by_two_det_surjective K),
    Subgroup.card_top, Nat.card_units, Nat.card_eq_fintype_card (α := K),
    ← Nat.card_congr (specialLinearDetKernelEquiv K), Matrix.card_GL_field] at hcard
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one] at hcard
  have hfactor : Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) := by
    rw [Nat.mul_sub_left_distrib, pow_two, mul_one]
  rw [hfactor] at hcard
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  apply mul_right_cancel₀ (show Fintype.card K - 1 ≠ 0 by omega)
  convert hcard using 1 <;> ring

theorem determinant_one_matrix_count (p : ℕ) (hp : p.Prime) :
    Nat.card {M : Matrix (Fin 2) (Fin 2) (ZMod p) // M.det = 1} =
      p * (p ^ 2 - 1) := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa only [ZMod.card] using specialLinear_two_card (ZMod p)

theorem solution (p : ℕ) (f : ℕ → ℕ)
    (h₀ : ∀ x, f x = (x ^ 2 - 1) * x) (_h₁ : Nat.Prime p) :
    f p = p * (p ^ 2 - 1) := by
  rw [h₀, mul_comm]
