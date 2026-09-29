-- Prove2me | solution 1 for LinearOptimization.simplex_pivot_basis_change
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-06T03:19:38.967547+00:00
-- url     : https://prove2.me/submissions/aabf575e-2caf-4ecb-8939-b6da54357ba4

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_LinearOptimization_SimplexPivot
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Matrix

private lemma inv_mulVec_basis_col {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n)
    [Invertible (LinearOptimization.basisMatrix A B)] (i : Fin m) :
    (LinearOptimization.basisMatrix A B)⁻¹.mulVec (fun r => A r (B i)) =
      Pi.single i 1 := by
  funext k
  have h : (LinearOptimization.basisMatrix A B)⁻¹.mulVec (fun r => A r (B i)) k =
      ((LinearOptimization.basisMatrix A B)⁻¹ *
        LinearOptimization.basisMatrix A B) k i := by
    simp [Matrix.mulVec, Matrix.mul_apply, dotProduct,
      LinearOptimization.basisMatrix]
  rw [h, Matrix.inv_mul_of_invertible]
  simp [Matrix.one_apply, Pi.single_apply]

private lemma basicDirection_entering {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n) (j : Fin n)
    (hj : j ∉ Set.range B) :
    LinearOptimization.basicDirection A B j j = 1 := by
  classical
  unfold LinearOptimization.basicDirection
  simp only [Pi.sub_apply, Pi.single_apply, Finset.sum_apply]
  have hsum : (∑ i : Fin m, (if j = B i then
      ((LinearOptimization.basisMatrix A B)⁻¹.mulVec (fun r => A r j)) i else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hji : j ≠ B i := by
      intro h
      exact hj ⟨i, h.symm⟩
    simp [hji]
  simp [hsum]

private lemma basicDirection_basic {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n) (j : Fin n)
    (hj : j ∉ Set.range B) (i : Fin m) :
    LinearOptimization.basicDirection A B j (B i) =
      -LinearOptimization.pivotColumn A B j i := by
  classical
  have hji : j ≠ B i := by
    intro h
    apply hj
    exact ⟨i, h.symm⟩
  unfold LinearOptimization.basicDirection LinearOptimization.pivotColumn
  simp [Pi.single_apply, hji, B.injective.eq_iff]

private lemma basicDirection_other {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n) (j k : Fin n)
    (hkj : k ≠ j) (hkB : k ∉ Set.range B) :
    LinearOptimization.basicDirection A B j k = 0 := by
  classical
  unfold LinearOptimization.basicDirection
  simp only [Pi.sub_apply, Pi.single_apply, Finset.sum_apply]
  have hsum : (∑ i : Fin m, (if k = B i then
      ((LinearOptimization.basisMatrix A B)⁻¹.mulVec (fun r => A r j)) i else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hki : k ≠ B i := by
      intro h
      exact hkB ⟨i, h.symm⟩
    simp [hki]
  simp [hkj, hsum]

private lemma basicDirection_kernel {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n) (j : Fin n)
    [Invertible (LinearOptimization.basisMatrix A B)] :
    A.mulVec (LinearOptimization.basicDirection A B j) = 0 := by
  classical
  unfold LinearOptimization.basicDirection
  change A.mulVec (Pi.single j 1 - ∑ i : Fin m,
    Pi.single (B i) (LinearOptimization.pivotColumn A B j i)) = 0
  rw [Matrix.mulVec_sub, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_single]
  have hsum : (∑ i : Fin m,
      MulOpposite.op (LinearOptimization.pivotColumn A B j i) •
        A.col (B i)) =
      (LinearOptimization.basisMatrix A B).mulVec
        (LinearOptimization.pivotColumn A B j) := by
    funext r
    simp [Matrix.mulVec, dotProduct, LinearOptimization.basisMatrix,
      LinearOptimization.pivotColumn,
      Matrix.col, mul_comm]
  rw [hsum]
  unfold LinearOptimization.pivotColumn
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible]
  ext r
  simp [Matrix.mulVec, Matrix.one_apply, Matrix.col]

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hA : LinearIndependent ℝ (fun i => A i))
    (B B' : Fin m ↪ Fin n) (hB : LinearOptimization.IsStdBasis A B)
    (x : Fin n → ℝ) (hx : x ∈ LinearOptimization.stdPolyhedron A b)
    (hxB : ∀ j ∉ Set.range B, x j = 0)
    (hnd : ¬LinearOptimization.IsStdDegenerateBasicSolution A b x)
    (j : Fin n) (hj : j ∉ Set.range B)
    (hcj : LinearOptimization.reducedCost A c B j < 0)
    (ℓ : Fin m) (hℓ : 0 < LinearOptimization.pivotColumn A B j ℓ)
    (hmin : ∀ i, 0 < LinearOptimization.pivotColumn A B j i →
      x (B ℓ) / LinearOptimization.pivotColumn A B j ℓ ≤
        x (B i) / LinearOptimization.pivotColumn A B j i)
    (hB'ne : ∀ i, i ≠ ℓ → B' i = B i) (hB'ℓ : B' ℓ = j) :
    LinearOptimization.IsStdBasis A B' ∧
    x + (x (B ℓ) / LinearOptimization.pivotColumn A B j ℓ) •
        LinearOptimization.basicDirection A B j ∈
      LinearOptimization.stdPolyhedron A b ∧
    ∀ k ∉ Set.range B',
      (x + (x (B ℓ) / LinearOptimization.pivotColumn A B j ℓ) •
        LinearOptimization.basicDirection A B j) k = 0 := by
  classical
  have hcols : LinearIndependent ℝ (LinearOptimization.basisMatrix A B).col := by
    simpa [Matrix.col, LinearOptimization.basisMatrix] using hB
  letI : Invertible (LinearOptimization.basisMatrix A B) :=
    (Matrix.linearIndependent_cols_iff_isUnit.mp hcols).invertible
  have hpivot_ne : LinearOptimization.pivotColumn A B j ℓ ≠ 0 := ne_of_gt hℓ
  have hnewcol : ∀ i : Fin m,
      (LinearOptimization.basisMatrix A B)⁻¹.mulVec (fun r => A r (B' i)) =
        if i = ℓ then LinearOptimization.pivotColumn A B j else Pi.single i 1 := by
    intro i
    by_cases hi : i = ℓ
    · subst i
      simp [hB'ℓ, LinearOptimization.pivotColumn]
    · rw [hB'ne i hi, inv_mulVec_basis_col]
      simp [hi]
  have hB' : LinearOptimization.IsStdBasis A B' := by
    apply Fintype.linearIndependent_iff.mpr
    intro g hg i
    have htrans := congrArg
      ((LinearOptimization.basisMatrix A B)⁻¹.mulVec) hg
    have htrans' : ∑ k : Fin m,
        g k • ((LinearOptimization.basisMatrix A B)⁻¹.mulVec (fun r => A r (B' k))) = 0 := by
      simpa [Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.transpose_apply] using htrans
    have hell := congrFun htrans' ℓ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hell
    simp_rw [hnewcol] at hell
    have hell' : g ℓ * LinearOptimization.pivotColumn A B j ℓ = 0 := by
      calc
        _ = ∑ k : Fin m,
            g k * (if k = ℓ then LinearOptimization.pivotColumn A B j
              else Pi.single k 1) ℓ := by
              symm
              rw [Finset.sum_eq_single ℓ]
              · simp
              · intro k _ hk
                simp [hk, Pi.single_apply, Ne.symm hk]
              · simp
        _ = 0 := hell
    have hgell : g ℓ = 0 := by
      apply (mul_eq_zero.mp hell').resolve_right hpivot_ne
    by_cases hi : i = ℓ
    · simpa [hi] using hgell
    · have hirow := congrFun htrans' i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hirow
      simp_rw [hnewcol] at hirow
      have hirow' : g i = 0 := by
        calc
          g i = ∑ k : Fin m,
              g k * (if k = ℓ then LinearOptimization.pivotColumn A B j
                else Pi.single k 1) i := by
                symm
                rw [Finset.sum_eq_single i]
                · simp [hi, Pi.single_apply]
                · intro k _ hki
                  by_cases hkℓ : k = ℓ
                  · subst k
                    simp [hgell]
                  · simp [hkℓ, Pi.single_apply, Ne.symm hki]
                · simp
          _ = 0 := hirow
      exact hirow'
  let θ : ℝ := x (B ℓ) / LinearOptimization.pivotColumn A B j ℓ
  let d : Fin n → ℝ := LinearOptimization.basicDirection A B j
  have hθ : 0 ≤ θ := by
    dsimp [θ]
    exact div_nonneg (hx.2 (B ℓ)) (le_of_lt hℓ)
  have hdker : A.mulVec d = 0 := by
    exact basicDirection_kernel A B j
  have hyfeas : x + θ • d ∈ LinearOptimization.stdPolyhedron A b := by
    constructor
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hx.1, hdker, smul_zero, add_zero]
    · intro k
      simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      dsimp [d]
      by_cases hkB : k ∈ Set.range B
      · obtain ⟨i, rfl⟩ := hkB
        rw [basicDirection_basic A B j hj i]
        change 0 ≤ x (B i) + θ * (-LinearOptimization.pivotColumn A B j i)
        by_cases hpi : 0 < LinearOptimization.pivotColumn A B j i
        · have hratio := hmin i hpi
          change θ ≤ x (B i) / LinearOptimization.pivotColumn A B j i at hratio
          have hprod : θ * LinearOptimization.pivotColumn A B j i ≤ x (B i) := by
            exact (le_div_iff₀ hpi).mp hratio
          linarith
        · have hpinonpos : LinearOptimization.pivotColumn A B j i ≤ 0 := le_of_not_gt hpi
          have hxnonneg := hx.2 (B i)
          exact add_nonneg hxnonneg (mul_nonneg hθ (neg_nonneg.mpr hpinonpos))
      · by_cases hkj : k = j
        · subst k
          rw [basicDirection_entering A B j hj]
          have hxj : x j = 0 := hxB j hj
          simp [hxj, hθ]
        · rw [basicDirection_other A B j k hkj hkB, hxB k hkB]
          simp
  refine ⟨hB', ?_⟩
  change x + θ • d ∈ LinearOptimization.stdPolyhedron A b ∧
    ∀ k ∉ Set.range B', (x + θ • d) k = 0
  refine ⟨hyfeas, ?_⟩
  intro k hkB'
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  dsimp [d]
  have hkj : k ≠ j := by
    intro h
    apply hkB'
    exact ⟨ℓ, by simpa [h] using hB'ℓ⟩
  by_cases hkexit : k = B ℓ
  · subst k
    rw [basicDirection_basic A B j hj ℓ]
    dsimp [θ]
    field_simp
    ring
  · have hkB : k ∉ Set.range B := by
      intro hk
      obtain ⟨i, hi⟩ := hk
      by_cases hiℓ : i = ℓ
      · subst i
        exact hkexit hi.symm
      · apply hkB'
        refine ⟨i, ?_⟩
        rw [hB'ne i hiℓ]
        exact hi
    rw [basicDirection_other A B j k hkj hkB, hxB k hkB]
    simp
