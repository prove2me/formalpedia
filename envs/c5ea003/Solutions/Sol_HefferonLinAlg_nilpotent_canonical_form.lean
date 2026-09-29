-- Prove2me | solution 1 for HefferonLinAlg.nilpotent_canonical_form
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-08-07T15:03:17.308633+00:00
-- url     : https://prove2.me/submissions/1449a00b-bdb9-418d-b34f-6bdedfb72b96

import Definitions.Def_HefferonLinAlg_jordan
import Theorems.Thm_HefferonLinAlg_nilpotent_string_basis
import Theorems.Thm_HefferonLinAlg_change_of_basis_gives_similar_matrices

open Matrix
open HefferonLinAlg

private theorem toMatrix_reindex_basis {K : Type*} [Field K] {n : ℕ}
    {J : Type*} [Fintype J] [DecidableEq J] {V : Type*} [AddCommGroup V] [Module K V]
    (b : Module.Basis J K V) (e : Fin n ≃ J) (g : V →ₗ[K] V) :
    LinearMap.toMatrix (b.reindex e.symm) (b.reindex e.symm) g
      = Matrix.reindex e.symm e.symm (LinearMap.toMatrix b b g) := by
  ext i j
  simp [LinearMap.toMatrix_apply, Module.Basis.reindex_apply,
    Module.Basis.repr_reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem solution {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (hA : IsNilpotent A) :
    ∃ (k : ℕ) (sz : Fin k → ℕ), IsJordanFormOf A sz (fun _ => (0 : K)) := by
  classical
  have hnil : IsNilpotent (Matrix.toLinAlgEquiv' A) :=
    hA.map (Matrix.toLinAlgEquiv' (R := K) (n := Fin n))
  obtain ⟨k, sz, b, hpos, hstr⟩ :=
    HefferonLinAlg.nilpotent_string_basis (Matrix.toLinAlgEquiv' A) hnil
  refine ⟨k, sz, hpos, ?_⟩
  have hcard : Fintype.card (jordanIndex sz) = n := by
    have h := Module.finrank_eq_card_basis b
    rw [Module.finrank_pi, Fintype.card_fin] at h
    exact h.symm
  refine ⟨(Fintype.equivFinOfCardEq hcard).symm, ?_⟩
  set e : Fin n ≃ jordanIndex sz := (Fintype.equivFinOfCardEq hcard).symm with he
  obtain ⟨P, hP, hPeq⟩ := HefferonLinAlg.change_of_basis_gives_similar_matrices
      (Pi.basisFun K (Fin n)) (b.reindex e.symm) (Matrix.toLinAlgEquiv' A)
  refine ⟨P, hP, ?_⟩
  have hBA : LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin n))
      (Matrix.toLinAlgEquiv' A) = A := by
    rw [LinearMap.toMatrix_eq_toMatrix']
    exact LinearMap.toMatrix'_toLin' A
  rw [hBA] at hPeq
  rw [← hPeq, toMatrix_reindex_basis]
  congr 1
  ext p q
  obtain ⟨i, x⟩ := p
  obtain ⟨j, y⟩ := q
  rw [LinearMap.toMatrix_apply, hstr]
  by_cases hij : i = j
  · subst hij
    rw [jordanMatrix_apply_same, jordanBlock_apply]
    by_cases hy : (y : ℕ) + 1 < sz i
    · rw [dif_pos hy, Module.Basis.repr_self, Finsupp.single_apply]
      by_cases hx : (x : ℕ) = (y : ℕ) + 1
      · have hxe : (⟨i, ⟨(y : ℕ) + 1, hy⟩⟩ : jordanIndex sz) = ⟨i, x⟩ := by
          simp [Sigma.mk.injEq, Fin.ext_iff, hx]
        rw [if_pos hxe, if_neg (by intro hc; rw [hc] at hx; omega : ¬ (x = y)),
          if_pos hx]
      · have hxe : ¬ ((⟨i, ⟨(y : ℕ) + 1, hy⟩⟩ : jordanIndex sz) = ⟨i, x⟩) := by
          simp [Sigma.mk.injEq, Fin.ext_iff]
          omega
        rw [if_neg hxe, if_neg hx]
        by_cases hxy : x = y
        · rw [if_pos hxy]
        · rw [if_neg hxy]
    · rw [dif_neg hy, map_zero, Finsupp.coe_zero, Pi.zero_apply]
      have hx : ¬ ((x : ℕ) = (y : ℕ) + 1) := by
        have := x.2
        omega
      rw [if_neg hx]
      by_cases hxy : x = y
      · rw [if_pos hxy]
      · rw [if_neg hxy]
  · rw [jordanMatrix_apply_ne _ _ _ _ hij]
    by_cases hy : (y : ℕ) + 1 < sz j
    · rw [dif_pos hy, Module.Basis.repr_self, Finsupp.single_apply]
      refine if_neg ?_
      simp [Sigma.mk.injEq]
      intro hc
      exact absurd hc.symm hij
    · rw [dif_neg hy, map_zero, Finsupp.coe_zero, Pi.zero_apply]
