-- Prove2me | Definitions.Def_mme_little_endian_kron_coordinate
-- name    : mme_little_endian_kron_coordinate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T04:45:40.410796+00:00
-- url     : https://prove2.me/theorems/de15d109-8b8f-4423-92b5-482e78b5e7b6
-- title:
--   Little-endian Kronecker coordinate equivalence
-- statement:
--   This interface identifies the tensor product of two coordinate-function spaces with a coordinate-function space on product dimensions, using the tail coordinate before the head coordinate. On standard basis vectors it sends\n\n$$\ne_{i,j} \\otimes e_{i^\\prime,j^\\prime} \\longmapsto e_{(i^\\prime,i),(j^\\prime,j)},\n$$\n\nwhere each ordered pair is encoded by the canonical finite-product equivalence. Recursing this convention yields the base-$P$ word coordinate $w_0+Pw_1+\\cdots+P^{m-1}w_{m-1}$ used for literal channel words.\n\nThis coordinate convention is reusable when a tensor-power restriction must preserve named positions, rather than merely identify spaces of equal dimension.\n\n**Formalization Note** The module includes the exact action on standard basis tensors; this is the coordinate lemma used by the accompanying MM tensor theorem.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.3 and Appendix A, https://arxiv.org/abs/2210.10173; coordinate encoding follows Mathlib finFunctionFinEquiv and finProdFinEquiv.

import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Logic.Equiv.Fin.Basic

open TensorProduct

namespace MME.DWZFineChannel

universe u

set_option autoImplicit false

private def littleEndianUncurryEquiv
    (K : Type u) [Field K]
    (α β γ : Type*) [AddCommGroup γ] [Module K γ] :
    (α → β → γ) ≃ₗ[K] (α × β → γ) where
  toFun f p := f p.1 p.2
  map_add' _ _ := by funext ⟨_, _⟩; rfl
  map_smul' _ _ := by funext ⟨_, _⟩; rfl
  invFun f a b := f (a, b)
  left_inv _ := by funext _ _; rfl
  right_inv _ := by funext ⟨_, _⟩; rfl

/-- A Kronecker equivalence whose recursive product coordinate is
`finProdFinEquiv (tail, head)`, hence little-endian. -/
noncomputable def littleEndianKronEquiv
    (K : Type u) [Field K] (a b c d : ℕ) :
    ((Fin a × Fin b → K) ⊗[K] (Fin c × Fin d → K)) ≃ₗ[K]
      (Fin (c * a) × Fin (d * b) → K) :=
  let e2 : ((Fin a × Fin b → K) ⊗[K] (Fin c × Fin d → K)) ≃ₗ[K]
      (Fin c × Fin d → (Fin a × Fin b → K)) :=
    TensorProduct.piScalarRight K K (Fin a × Fin b → K) (Fin c × Fin d)
  let e3 : (Fin c × Fin d → (Fin a × Fin b → K)) ≃ₗ[K]
      ((Fin c × Fin d) × (Fin a × Fin b) → K) :=
    littleEndianUncurryEquiv K (Fin c × Fin d) (Fin a × Fin b) K
  let reindex :
      (Fin c × Fin a) × (Fin d × Fin b) ≃
        (Fin c × Fin d) × (Fin a × Fin b) := {
    toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
    invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
    left_inv x := by rcases x with ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl
    right_inv x := by rcases x with ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl
  }
  let e4 : ((Fin c × Fin d) × (Fin a × Fin b) → K) ≃ₗ[K]
      ((Fin c × Fin a) × (Fin d × Fin b) → K) :=
    LinearEquiv.funCongrLeft K K reindex
  let e5 : ((Fin c × Fin a) × (Fin d × Fin b) → K) ≃ₗ[K]
      (Fin (c * a) × Fin (d * b) → K) :=
    LinearEquiv.funCongrLeft K K
      (Equiv.prodCongr finProdFinEquiv.symm finProdFinEquiv.symm)
  e2.trans (e3.trans (e4.trans e5))

theorem littleEndianKronEquiv_single
    (K : Type u) [Field K] {a b c d : ℕ}
    (i : Fin a) (j : Fin b) (i' : Fin c) (j' : Fin d) :
    littleEndianKronEquiv K a b c d
        ((Pi.single (i, j) 1) ⊗ₜ[K] (Pi.single (i', j') 1)) =
      Pi.single (finProdFinEquiv (i', i), finProdFinEquiv (j', j)) 1 := by
  funext IJ
  obtain ⟨I, J⟩ := IJ
  have lhs_val :
      (littleEndianKronEquiv K a b c d
          ((Pi.single (i, j) 1) ⊗ₜ[K] (Pi.single (i', j') 1))) (I, J) =
        ((Pi.single (i', j') 1 : Fin c × Fin d → K)
            ((finProdFinEquiv.symm I).1, (finProdFinEquiv.symm J).1)) *
          ((Pi.single (i, j) 1 : Fin a × Fin b → K)
            ((finProdFinEquiv.symm I).2, (finProdFinEquiv.symm J).2)) := by
    simp only [littleEndianKronEquiv, littleEndianUncurryEquiv,
      LinearEquiv.trans_apply, LinearEquiv.coe_mk,
      LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul,
      Equiv.prodCongr_apply, Prod.map_apply]
    rfl
  rw [lhs_val]
  simp only [Pi.single_apply, Prod.mk.injEq]
  set I' : Fin c × Fin a := finProdFinEquiv.symm I with hIdef
  set J' : Fin d × Fin b := finProdFinEquiv.symm J with hJdef
  have hIeq : I = finProdFinEquiv I' := by
    rw [hIdef]
    exact (finProdFinEquiv.apply_symm_apply I).symm
  have hJeq : J = finProdFinEquiv J' := by
    rw [hJdef]
    exact (finProdFinEquiv.apply_symm_apply J).symm
  rw [hIeq, hJeq]
  simp only [finProdFinEquiv.injective.eq_iff]
  obtain ⟨I'1, I'2⟩ := I'
  obtain ⟨J'1, J'2⟩ := J'
  by_cases hI1 : I'1 = i'
  · by_cases hJ1 : J'1 = j'
    · by_cases hI2 : I'2 = i
      · by_cases hJ2 : J'2 = j
        · simp [hI1, hJ1, hI2, hJ2]
        · simp [hI1, hJ1, hI2, hJ2]
      · simp [hI1, hJ1, hI2]
    · simp [hI1, hJ1]
  · simp [hI1]

end MME.DWZFineChannel


