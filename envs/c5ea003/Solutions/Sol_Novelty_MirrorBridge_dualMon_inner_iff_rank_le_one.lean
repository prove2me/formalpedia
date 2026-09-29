-- Prove2me | solution 1 for Novelty.MirrorBridge.dualMon_inner_iff_rank_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T15:37:04.371457+00:00
-- url     : https://prove2.me/submissions/938e7411-eae6-4b6e-bb5d-afde67bc1547

import Mathlib
import Definitions.Def_Novelty_SYZDualityRankN
import Definitions.Def_Novelty_SYZMonodromyDuality

open Novelty.MirrorBridge Matrix in
theorem solution (n : ℕ) :
    (∃ S : IntGL n, ∀ M : IntGL n, dualMon M = S * M * S⁻¹) ↔ n ≤ 1 := by
  constructor
  · -- traces: conjugation preserves `tr M`, while `tr (M⁻¹)ᵀ = tr M⁻¹` can differ
    rintro ⟨S, hS⟩
    by_contra hn
    replace hn : 2 ≤ n := by omega
    let a : Fin n := ⟨0, by omega⟩
    let b : Fin n := ⟨1, by omega⟩
    have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
    -- `A = [[1,1],[1,0]] ⊕ 1`, `B = A⁻¹ = [[0,1],[1,-1]] ⊕ 1`
    let X : Matrix (Fin n) (Fin n) ℤ := single a b 1 + single b a 1 + single b b (-1)
    let Y : Matrix (Fin n) (Fin n) ℤ :=
      single a b 1 + single b a 1 + single a a (-1) + single b b (-2)
    have hXY : X * Y = -(X + Y) := by
      have hba : b ≠ a := hab.symm
      simp only [X, Y, add_mul, mul_add, Matrix.single_mul_single_same,
        Matrix.single_mul_single_of_ne, hab, hba, ne_eq, not_false_eq_true,
        add_zero, zero_add]
      ext k l
      simp only [add_apply, neg_apply, Matrix.single_apply]
      by_cases hk : a = k <;> by_cases hl : a = l <;> by_cases hk' : b = k <;>
        by_cases hl' : b = l <;> simp_all
    have hYX : Y * X = -(X + Y) := by
      have hba : b ≠ a := hab.symm
      simp only [X, Y, add_mul, mul_add, Matrix.single_mul_single_same,
        Matrix.single_mul_single_of_ne, hab, hba, ne_eq, not_false_eq_true,
        add_zero, zero_add]
      ext k l
      simp only [add_apply, neg_apply, Matrix.single_apply]
      by_cases hk : a = k <;> by_cases hl : a = l <;> by_cases hk' : b = k <;>
        by_cases hl' : b = l <;> simp_all
    let M : IntGL n :=
      { val := 1 + X
        inv := 1 + Y
        val_inv := by
          rw [add_mul, one_mul, mul_add, mul_one, hXY]
          abel
        inv_val := by
          rw [add_mul, one_mul, mul_add, mul_one, hYX]
          abel }
    have htr := congrArg (fun U : IntGL n => trace (U : Matrix (Fin n) (Fin n) ℤ)) (hS M)
    simp only [dualMon] at htr
    rw [trace_transpose, Units.val_mul, Units.val_mul, trace_mul_comm, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul] at htr
    have hinv : ((M⁻¹ : IntGL n) : Matrix (Fin n) (Fin n) ℤ) = 1 + Y := rfl
    have hval : ((M : IntGL n) : Matrix (Fin n) (Fin n) ℤ) = 1 + X := rfl
    rw [hinv, hval] at htr
    have hba : b ≠ a := hab.symm
    simp only [X, Y, trace_add, trace_one, trace_single_eq_same, trace_single_eq_of_ne, hab, hba,
      ne_eq, not_false_eq_true, Fintype.card_fin] at htr
    omega
  · -- for `n ≤ 1` every matrix is symmetric and `M⁻¹ = M`
    intro hn
    refine ⟨1, fun M => ?_⟩
    rw [one_mul, inv_one, mul_one]
    apply Units.ext
    show ((M⁻¹ : IntGL n) : Matrix (Fin n) (Fin n) ℤ)ᵀ = M
    have hsymm : ∀ A : Matrix (Fin n) (Fin n) ℤ, Aᵀ = A := by
      intro A
      ext i j
      have : i = j := Fin.ext (by omega)
      subst this
      rfl
    rw [hsymm]
    ext i j
    have hij : i = j := Fin.ext (by omega)
    subst hij
    have hprod := congrFun (congrFun (M.inv_val) i) i
    rw [mul_apply, one_apply_eq] at hprod
    have huniq : ∀ k : Fin n, k = i := fun k => Fin.ext (by omega)
    rw [Fintype.sum_eq_single i (fun k hk => absurd (huniq k) hk)] at hprod
    change M.inv i i = (M : Matrix (Fin n) (Fin n) ℤ) i i
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1, h2]
