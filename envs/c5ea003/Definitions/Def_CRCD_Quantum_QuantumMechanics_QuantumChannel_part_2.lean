-- Prove2me | Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumChannel_part_2
-- name    : CRCD_Quantum_QuantumMechanics_QuantumChannel_part_2
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T23:47:49.587217+00:00
-- url     : https://prove2.me/theorems/fa5699bd-1d20-4ec4-8be5-f2135cbbf6ee
-- title:
--   Kraus representations, rank-sized spectral decompositions, and a dilation operator
-- statement:
--   Let $H_1,H_2$ be finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal L(H_1)\to\mathcal L(H_2)$ be a complex-linear superoperator. Using the positivity and tensor interfaces provided previously, this part defines positivity of $\Phi\otimes\mathrm{id}_{H_1}$, positivity of its Choi operator for a finite input basis $b$, and finite Kraus representations:
--   $$
--   \Phi(X)=\sum_{a\in\kappa} A_aXA_a^*,\qquad A_a:H_1\to H_2.
--   $$
--   The finite index set $\kappa$ may be empty. The predicate $\mathrm{HasRankKraus}_b(\Phi)$ requires such a representation with $|\kappa|=\operatorname{rank}C_b(\Phi)$, where rank is the complex dimension of the Choi operator's range; forgetting that equality gives $\mathrm{HasKraus}(\Phi)$. Every individual Kraus term, and every finite sum of them, is proved completely positive. Complete positivity also implies positivity of $\Phi\otimes\mathrm{id}_{H_1}$. The proofs use an orthonormal-basis isometry between a finite Hilbert direct sum and the tensor product, intertwining the corresponding matrix and tensor amplifications.
--
--   For any positive operator $T$ on a finite-dimensional complex Hilbert space $E$, the spectral construction supplies a finite family with exactly $\operatorname{rank}T$ members such that
--   $$
--   T=\sum_a |u_a\rangle\langle u_a|.
--   $$
--   A full-dimensional version includes zero vectors at zero eigenvalues, and the reduced version indexes only nonzero eigenvalues. This part also defines conjugation of endomorphisms by a linear equivalence, the partial trace $\mathrm{Tr}_{\mathrm{right}}$ over the second tensor factor, and the dilation operator associated to a Kraus family:
--   $$
--   W x=\sum_{a\in\kappa} A_a x\otimes e_a
--   \quad\text{in }H_2\otimes\mathbb C^{\kappa}.
--   $$
--   It proves formulas for $W$, its adjoint and their compositions, and identifies the environment dimension with $|\kappa|$. No trace-preservation or isometry assumption on $W$ is imposed here. Additional basis and rank-one expansions express arbitrary finite-dimensional linear maps as finite sums of outer products.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumMechanics/QuantumChannel.lean#L956-L1631

import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumChannel_part_1
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumState

/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/








-- These typeclasses are kept on several declarations as part of a stable API
-- (e.g. matching downstream signatures), even when the type does not literally
-- mention them; silence the Mathlib hygiene linters for the whole file.
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace QuantumChannel

open QuantumState
open TensorProduct

universe u v w

section Definition

-- The set of linear maps


section ContinuousLinearMapsAreCStarAlgebras





















end ContinuousLinearMapsAreCStarAlgebras


-- The structure of quantum channels


variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

-- def: Partial trace (1.121) https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
-- Tr₂(X) for X ∈ L(ℋ₁⊗ℋ₂)







-- It may be neccesary to add some lemmas to use l_tensor_equiv effectively















-- def: vec(A) (1.127) https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
-- vec[|u⟩⟨v|] := |u⟩⊗|v⟩ : (ℋ₁ →L[ℂ] ℋ₂) → ℋ₂⊗ℋ₁






-- (1.131) (1.132) https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
-- Lemma 5.12 http://www.ueltschi.org/AZschool/notes/EricCarlen.pdf
-- For any qudit ℋ, any A,B ∈ L(ℋ), and any K ∈ L(ℋ),
-- ⟨ vec[K] ∣ (A ⊗ B) vec[K] ⟩ = Tr[K† A K B.transpose]






















-- def: Choi operator (2.64) https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- J(Φ) := (Φ⊗id)(vec[I(ℋ₂⊗ℋ₁)] vec[I(ℋ₂⊗ℋ₁)]†) for Φ ∈ T(ℋ₁,ℋ₂)

-- (1.57) in https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf












end Definition

section RepresentationsOfChannels

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]

-- Proposition 2.17 https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudit ℋ, and any P ∈ Pos(ℋ),
-- the map Φ(α):=αP ∈ T(ℂ,ℋ) is a completely positive ContinuourLinearMap.

-- Proposition 2.18 and its remark https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudits ℋ₁, ℋ₂, and any Φ ∈ T(ℋ₁,ℋ₂),
-- if Φ is a completely positive ContinuourLinearMap,
-- the adjoint map of Φ is a completely positive ContinuourLinearMap.

-- Corollary 2.19 https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudit ℋ, Tr ∈ T(ℋ,ℂ) is a completely positive ContinuourLinearMap.

-- Proposition 2.20 https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudits ℋ₁, ℋ₂, and any Φ ∈ T(ℋ₁,ℋ₂),
-- J(Φ)=∑_{a∈Σ} vec(Aₐ) vec(Bₐ)†
-- if and only if
-- for ℋ₃=ℂ^Σ, A,B∈(ℋ₁→L[ℂ]ℋ₂⊗ℋ₃) defined as
-- A=∑_{a∈Σ}Aₐ⊗eₐ,
-- B=∑_{a∈Σ}Aₐ⊗eₐ,
-- it holds for all X∈L(X) that
-- Φ(X)=Tr₃[Aₐ X Bₐ†]

-- Theorem 2.22 https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudits ℋ₁, ℋ₂, and any Φ ∈ T(ℋ₁,ℋ₂), the following statements are equivalent:
-- 1: Φ is a completely positive ContinuosLinearMap;
-- 2: J(Φ) ∈ Pos(ℋ₂⊗ℋ₁);
-- 3: ∃qudit ℋ₃, ∃A∈(ℋ₁→L[ℂ]ℋ₂⊗ℋ₃), Φ(X)=Tr₃[A X A†]





variable {ι : Type*} [DecidableEq ι] [Fintype ι]























































































noncomputable def linearToContinuousEndStarAlgEquiv
    (ℋ : Type*) [Qudit ℋ] :
    L ℋ ≃⋆ₐ[ℂ] (ℋ →L[ℂ] ℋ) where
  toFun := LinearMap.toContinuousLinearMap
  invFun := ContinuousLinearMap.toLinearMap
  left_inv := by intro A; rfl
  right_inv := by intro A; ext x; rfl
  map_mul' := by intro A B; rfl
  map_add' := by intro A B; rfl
  map_smul' := by intro c A; rfl
  map_star' := by
    intro A
    simpa using (LinearMap.adjoint_toContinuousLinearMap (A := A))

noncomputable def basisPiTensorLinearEquiv
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) :
    DS n ℋ₂ ≃ₗ[ℂ] ℋ₂ ⊗[ℂ] ℋ₁ :=
  (dsEquiv n ℋ₂).toLinearEquiv.trans <|
    ((Finsupp.linearEquivFunOnFinite ℂ ℋ₂ (Fin n)).symm.trans
      (TensorProduct.equivFinsuppOfBasisRight b.toBasis).symm)

lemma basisPiTensorLinearEquiv_apply
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) (x : DS n ℋ₂) :
    basisPiTensorLinearEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b x =
      ∑ i, dsProj n ℋ₂ i x ⊗ₜ[ℂ] b i := by
  rw [basisPiTensorLinearEquiv]
  change
    (TensorProduct.equivFinsuppOfBasisRight b.toBasis).symm
        ((Finsupp.linearEquivFunOnFinite ℂ ℋ₂ (Fin n)).symm ((dsEquiv n ℋ₂) x)) =
      ∑ i, dsProj n ℋ₂ i x ⊗ₜ[ℂ] b i
  rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply]
  simp [Finsupp.sum_fintype, dsProj, dsEquiv]

lemma basisPiTensorLinearEquiv_dsIncl
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) (i : Fin n) (x : ℋ₂) :
    basisPiTensorLinearEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b (dsIncl n ℋ₂ i x) =
      x ⊗ₜ[ℂ] b i := by
  rw [basisPiTensorLinearEquiv_apply]
  classical
  rw [Finset.sum_eq_single i]
  · simp [dsProj_dsIncl_apply]
  · intro j _ hji
    simp [dsProj_dsIncl_apply, hji]
  · simp

lemma basisPiTensorLinearEquiv_inner
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) (x y : DS n ℋ₂) :
    inner ℂ
        (basisPiTensorLinearEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b x)
        (basisPiTensorLinearEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b y) =
      inner ℂ x y := by
  rw [basisPiTensorLinearEquiv_apply, basisPiTensorLinearEquiv_apply]
  classical
  simp only [inner_sum, sum_inner, TensorProduct.inner_tmul]
  simpa [PiLp.inner_apply] using
    (b.orthonormal.inner_left_right_finset
      (s := Finset.univ)
      (a := fun i j => inner ℂ (dsProj n ℋ₂ j x) (dsProj n ℋ₂ i y)))

noncomputable def basisPiTensorLinearIsometryEquiv
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) :
    DS n ℋ₂ ≃ₗᵢ[ℂ] ℋ₂ ⊗[ℂ] ℋ₁ :=
  (basisPiTensorLinearEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b).isometryOfInner
    (basisPiTensorLinearEquiv_inner (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b)

noncomputable def basisPiTensorEndAlgEquiv
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) :
    L (DS n ℋ₂) ≃⋆ₐ[ℂ] L (ℋ₂ ⊗[ℂ] ℋ₁) :=
  (linearToContinuousEndStarAlgEquiv (ℋ := DS n ℋ₂)).trans <|
    ((basisPiTensorLinearIsometryEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b).conjStarAlgEquiv.trans
      (linearToContinuousEndStarAlgEquiv (ℋ := ℋ₂ ⊗[ℂ] ℋ₁)).symm)

lemma basisPiTensorLinearIsometryEquiv_apply
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) (x : DS n ℋ₂) :
    basisPiTensorLinearIsometryEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b x =
      ∑ i, dsProj n ℋ₂ i x ⊗ₜ[ℂ] b i := by
  simpa using basisPiTensorLinearEquiv_apply (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b x

lemma basisPiTensorLinearIsometryEquiv_dsIncl
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) (i : Fin n) (x : ℋ₂) :
    basisPiTensorLinearIsometryEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b (dsIncl n ℋ₂ i x) =
      x ⊗ₜ[ℂ] b i := by
  exact basisPiTensorLinearEquiv_dsIncl (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b i x

lemma basisPiTensorLinearIsometryEquiv_symm_tmul
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) (i : Fin n) (x : ℋ₂) :
    (basisPiTensorLinearIsometryEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b).symm (x ⊗ₜ[ℂ] b i) =
      dsIncl n ℋ₂ i x := by
  apply (basisPiTensorLinearIsometryEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b).injective
  simpa using
    (basisPiTensorLinearIsometryEquiv_dsIncl (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b i x).symm

lemma basisPiTensorEndAlgEquiv_apply_apply
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁)
    (A : L (DS n ℋ₂)) (z : ℋ₂ ⊗[ℂ] ℋ₁) :
    basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b A z =
      basisPiTensorLinearIsometryEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b
        (A ((basisPiTensorLinearIsometryEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b).symm z)) := by
  rfl

lemma basisPiTensorEndAlgEquiv_apply_tmul_basis
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁)
    (A : L (DS n ℋ₂)) (x : ℋ₂) (j : Fin n) :
    basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b A (x ⊗ₜ[ℂ] b j) =
      ∑ i : Fin n, ((ampCStarEquiv n ℋ₂ A) i j) x ⊗ₜ[ℂ] b i := by
  rw [basisPiTensorEndAlgEquiv_apply_apply]
  rw [basisPiTensorLinearIsometryEquiv_symm_tmul]
  rw [basisPiTensorLinearIsometryEquiv_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  have hcoord :
      dsProj n ℋ₂ i (A (dsIncl n ℋ₂ j x)) =
        ampPlainEquiv n ℋ₂ A i j x := by
    symm
    exact ampPlainEquiv_apply_apply_ds
      (k := n) (ℋ := ℋ₂) (f := A) (i := i) (j := j) (x := x)
  rw [hcoord]
  rfl



lemma basisPiTensorEndAlgEquiv_expansion
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁)
    (A : L (DS n ℋ₂)) :
    basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b A =
      ∑ i : Fin n, ∑ j : Fin n,
        (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
          (((ampCStarEquiv n ℋ₂ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i)) := by
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro x v
    calc
      basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b A (x ⊗ₜ[ℂ] v) =
          ∑ j : Fin n,
            (b.repr v j) •
              basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b A (x ⊗ₜ[ℂ] b j) := by
          conv_lhs => rw [← b.sum_repr v]
          simp [TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_sum]
      _ =
          ∑ j : Fin n,
            (b.repr v j) •
              ∑ i : Fin n, ((ampCStarEquiv n ℋ₂ A) i j) x ⊗ₜ[ℂ] b i := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [basisPiTensorEndAlgEquiv_apply_tmul_basis]
      _ =
          ∑ i : Fin n, ∑ j : Fin n,
            (b.repr v j) • (((ampCStarEquiv n ℋ₂ A) i j) x ⊗ₜ[ℂ] b i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro i _
          simp [Finset.smul_sum]
      _ =
          (∑ i : Fin n, ∑ j : Fin n,
            (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
              (((ampCStarEquiv n ℋ₂ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i))) (x ⊗ₜ[ℂ] v) := by
          simp only [LinearMap.sum_apply]
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [l_tensor_equiv_symm_tmul]
          simp [outer_product, dualTensorHom_apply, TensorProduct.tmul_smul,
            OrthonormalBasis.repr_apply_apply]
  · intro z w hz hw
    simp only [hz, hw, map_add]

lemma basisPiTensorEndAlgEquiv_ampSuper
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁)
    (Φ : T ℋ₁ ℋ₂) (A : L (DS n ℋ₁)) :
    basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b (ampSuper n Φ A) =
      amplifyWithId Φ (basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁) n b A) := by
  rw [basisPiTensorEndAlgEquiv_expansion (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b (ampSuper n Φ A)]
  rw [basisPiTensorEndAlgEquiv_expansion (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁) n b A]
  simp only [amplifyWithId, LinearMap.comp_apply, map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  have hentry :
      (ampCStarEquiv n ℋ₂ (ampSuper n Φ A)) i j =
        Φ ((ampCStarEquiv n ℋ₁ A) i j) := by
    have h := congrFun (congrFun (ampCStarEquiv_ampSuper_apply (k := n) (Φ := Φ) (A := A)) i) j
    simpa [CStarMatrix.map_apply] using h
  have hterm :
      ((ampCStarEquiv n ℋ₂ (ampSuper n Φ A)) i j) ⊗ₜ[ℂ] outer_product (b j) (b i) =
        Φ ((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i) := by
    exact congrArg (fun B : L ℋ₂ => B ⊗ₜ[ℂ] outer_product (b j) (b i)) hentry
  have hcancel :
      (l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁))
          ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁)).symm
            (((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i))) =
        ((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i) := by
    exact LinearEquiv.apply_symm_apply (l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁))
      (((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i))
  apply (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).injective
  rw [LinearEquiv.apply_symm_apply]
  have houter :
      (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁))
          ((l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
            ((TensorProduct.map Φ LinearMap.id)
              ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁))
                ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁)).symm
                  (((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i)))))) =
        (TensorProduct.map Φ LinearMap.id)
          ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁))
            ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁)).symm
              (((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i)))) := by
    exact LinearEquiv.apply_symm_apply (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁))
      ((TensorProduct.map Φ LinearMap.id)
        ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁))
          ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁)).symm
            (((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i)))))
  change
      ((ampCStarEquiv n ℋ₂ (ampSuper n Φ A)) i j) ⊗ₜ[ℂ] outer_product (b j) (b i) =
        (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁))
          ((l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
            ((TensorProduct.map Φ LinearMap.id)
              ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁))
                ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁)).symm
                  (((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i))))))
  rw [houter]
  rw [hcancel]
  rw [TensorProduct.map_tmul]
  exact hterm

lemma ampSuper_krausTerm_eq
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) :
    ampSuper k (krausTerm V) = krausTerm (ampKrausFactor k V) := by
  apply LinearMap.ext
  intro A
  apply (ampCStarEquiv k ℋ₂).injective
  trans (ampCStarEquiv k ℋ₁ A).map (krausTerm V)
  · simpa using ampCStarEquiv_ampSuper_apply (k := k) (Φ := krausTerm V) (A := A)
  ext i j x
  change (((ampCStarEquiv k ℋ₁ A).map (krausTerm V)) i j) x =
    ampPlainEquiv k ℋ₂ ((krausTerm (ampKrausFactor k V)) A) i j x
  rw [ampPlainEquiv_apply_apply_ds]
  have hentry :
      (ampCStarEquiv k ℋ₁ A i j) (V.adjoint x) =
        dsProj k ℋ₁ i (A (dsIncl k ℋ₁ j (V.adjoint x))) := by
    simpa using
      (ampPlainEquiv_apply_apply_ds (k := k) (ℋ := ℋ₁) (f := A) (i := i) (j := j)
        (x := V.adjoint x)).symm
  simp [CStarMatrix.map_apply, krausTerm, dsProj_ampKrausFactor,
    ampKrausFactor_adjoint_dsIncl, hentry]

lemma krausTerm_isCompletelyPositive
    (V : ℋ₁ →ₗ[ℂ] ℋ₂) :
    IsCompletelyPositive (krausTerm V) := by
  refine (isCompletelyPositive_iff_cstarMatrix_nonneg (krausTerm V)).mpr ?_
  intro k M hM
  have hK : IsKPositive k (krausTerm V) := by
    exact (isKPositive_iff_isPositiveMap_ampSuper (k := k) (Φ := krausTerm V)).mpr <| by
      simpa [ampSuper_krausTerm_eq] using
        krausTerm_isPositiveMap (V := ampKrausFactor k V)
  exact hK M hM

lemma sum_krausTerm_isCompletelyPositive
    {σ : Type*} [Fintype σ]
    (V : σ → (ℋ₁ →ₗ[ℂ] ℋ₂)) :
    IsCompletelyPositive (∑ r, krausTerm (V r)) := by
  classical
  refine (isCompletelyPositive_iff_cstarMatrix_nonneg (∑ r, krausTerm (V r))).mpr ?_
  intro k M hM
  have hmap : M.map (∑ r, (krausTerm (V r) : T ℋ₁ ℋ₂)) = ∑ r, M.map (krausTerm (V r)) := by
    have hmapFin (s : Finset σ) :
        M.map (Finset.sum s fun r => (krausTerm (V r) : T ℋ₁ ℋ₂)) =
          Finset.sum s fun r => M.map (krausTerm (V r)) := by
      ext i j x
      induction s using Finset.induction_on with
      | empty =>
          simp [CStarMatrix.map_apply]
      | @insert a s ha ih =>
          simp [Finset.sum_insert, ha, CStarMatrix.map_apply, LinearMap.sum_apply]
          simpa [CStarMatrix.map_apply, LinearMap.sum_apply] using ih
    simpa using hmapFin Finset.univ
  simpa [hmap] using
    (Finset.sum_nonneg fun r _ =>
      (isCompletelyPositive_iff_cstarMatrix_nonneg (krausTerm (V r))).mp
        (krausTerm_isCompletelyPositive (V r)) k M hM)

def AmplificationPositive (Φ : T ℋ₁ ℋ₂) : Prop :=
  IsPositiveMap (amplifyWithId Φ)

lemma cp_amplify
    (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ → AmplificationPositive Φ := by
  intro hΦ X hX
  let n := Module.finrank ℂ ℋ₁
  let b : OrthonormalBasis (Fin n) ℂ ℋ₁ := stdOrthonormalBasis ℂ ℋ₁
  let e₁ := basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁) n b
  let e₂ := basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b
  let A : L (DS n ℋ₁) := e₁.symm X
  have hA : 0 ≤ A := by
    have hX' : 0 ≤ e₁ A := by
      simpa [A, e₁] using hX
    exact (starAlgEquiv_nonneg_iff e₁).1 hX'
  have hK : IsKPositive n Φ :=
    (isCompletelyPositive_iff_cstarMatrix_nonneg Φ).mp hΦ n
  have hAmp : 0 ≤ ampSuper n Φ A :=
    (isKPositive_iff_isPositiveMap_ampSuper (k := n) (Φ := Φ)).mp hK A hA
  have hTensor : 0 ≤ e₂ (ampSuper n Φ A) :=
    starAlgEquiv_nonneg e₂ hAmp
  have hEq : e₂ (ampSuper n Φ A) = amplifyWithId Φ X := by
    simpa [A, e₁, e₂] using
      (basisPiTensorEndAlgEquiv_ampSuper (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b Φ A)
  simpa [hEq] using hTensor

def ChoiPositive (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) : Prop :=
  0 ≤ choi b Φ

def KrausRep (Φ : T ℋ₁ ℋ₂) (κ : Type*) [DecidableEq κ] [Fintype κ] : Prop :=
  ∃ A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂),
    ∀ X : L ℋ₁, Φ X = ∑ a : κ, (A a).comp (X.comp (LinearMap.adjoint (A a)))

theorem fixed_kraus_to_cp
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (Φ : T ℋ₁ ℋ₂) :
    KrausRep Φ κ → IsCompletelyPositive Φ := by
  rintro ⟨A, hA⟩
  have hΦ : Φ = ∑ a : κ, krausTerm (A a) := by
    apply LinearMap.ext
    intro X
    simpa [krausTerm] using hA X
  rw [hΦ]
  exact sum_krausTerm_isCompletelyPositive A

noncomputable def choiRank (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) : ℕ :=
  Module.finrank ℂ (LinearMap.range (choi b Φ))

def HasKraus (Φ : T ℋ₁ ℋ₂) : Prop :=
  ∃ (κ : Type u) (_ : DecidableEq κ) (_ : Fintype κ),
    @KrausRep ℋ₁ ℋ₂ _ _ Φ κ _ _

def HasRankKraus (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) : Prop :=
  ∃ (κ : Type u) (dec : DecidableEq κ) (inst : Fintype κ),
    Fintype.card κ = choiRank b Φ ∧
      @KrausRep ℋ₁ ℋ₂ _ _ Φ κ dec inst

lemma positive_full_spectral_outer_product
    {E : Type*} [Qudit E] (T : L E) (hT : 0 ≤ T) :
    let n := Module.finrank ℂ E
    let hTpos : T.IsPositive := (LinearMap.nonneg_iff_isPositive T).mp hT
    let hSym : T.IsSymmetric := hTpos.isSymmetric
    ∃ u : Fin n → E,
      T = ∑ i : Fin n, outer_product (u i) (u i) ∧
        ∀ i : Fin n, hSym.eigenvalues rfl i = 0 → u i = 0 := by
  classical
  dsimp
  let n := Module.finrank ℂ E
  let hTpos : T.IsPositive := (LinearMap.nonneg_iff_isPositive T).mp hT
  let hSym : T.IsSymmetric := hTpos.isSymmetric
  let u : Fin n → E :=
    fun i => ((hSym.eigenvalues rfl i).sqrt : ℂ) • hSym.eigenvectorBasis rfl i
  refine ⟨u, ?_, ?_⟩
  · ext x
    rw [show (∑ i : Fin n, outer_product (u i) (u i)) x =
        ∑ i : Fin n, inner ℂ (u i) x • u i by
      simp [outer_product_eq_rankOne]]
    simp_rw [u]
    simp_rw [inner_smul_left]
    simp_rw [smul_smul]
    simp_rw [mul_assoc]
    simp_rw [Complex.conj_ofReal]
    simp_rw [mul_comm (inner ℂ _ _)]
    simp_rw [← mul_assoc]
    simp_rw [← Complex.ofReal_mul]
    simp_rw [← Real.sqrt_mul (hTpos.nonneg_eigenvalues rfl _)]
    simp_rw [Real.sqrt_mul_self (hTpos.nonneg_eigenvalues rfl _)]
    simp_rw [mul_comm _ (inner ℂ _ _)]
    simp_rw [← smul_eq_mul]
    simp_rw [smul_assoc]
    have happly :
        ∀ i : Fin n,
          (hSym.eigenvalues rfl i : ℂ) • hSym.eigenvectorBasis rfl i =
            T (hSym.eigenvectorBasis rfl i) := by
      intro i
      exact (hSym.apply_eigenvectorBasis rfl i).symm
    simp_rw [happly]
    simp_rw [← map_smul]
    simp_rw [← map_sum]
    simp_rw [← OrthonormalBasis.repr_apply_apply]
    simp_rw [OrthonormalBasis.sum_repr]
  · intro i hi
    change ((hSym.eigenvalues rfl i).sqrt : ℂ) • hSym.eigenvectorBasis rfl i = 0
    simp [hi]

lemma positive_spectral_outer_product
    {E : Type*} [Qudit E] (T : L E) (hT : 0 ≤ T) :
    let n := Module.finrank ℂ E
    let hTpos : T.IsPositive := (LinearMap.nonneg_iff_isPositive T).mp hT
    let hSym : T.IsSymmetric := hTpos.isSymmetric
    ∃ u : { i : Fin n // hSym.eigenvalues rfl i ≠ 0 } → E,
      T = ∑ a, outer_product (u a) (u a) := by
  dsimp
  let n := Module.finrank ℂ E
  let hTpos : T.IsPositive := (LinearMap.nonneg_iff_isPositive T).mp hT
  let hSym : T.IsSymmetric := hTpos.isSymmetric
  let p : Fin n → Prop := fun i => hSym.eigenvalues rfl i ≠ 0
  obtain ⟨u, hsum, hzero⟩ :=
    positive_full_spectral_outer_product (T := T) (hT := hT)
  refine ⟨fun a => u a, ?_⟩
  have hzero_sum :
      (∑ a : { i : Fin n // ¬ p i }, outer_product (u a) (u a)) = 0 := by
    apply Fintype.sum_eq_zero
    intro a
    have ha : hSym.eigenvalues rfl a = 0 := not_not.mp a.property
    simp [hzero a ha, outer_product]
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype p
      (fun i : Fin n => outer_product (u i) (u i))
  calc
    T = ∑ i : Fin n, outer_product (u i) (u i) := hsum
    _ = ∑ a : { i : Fin n // p i }, outer_product (u a) (u a) := by
      rw [← hsplit, hzero_sum, add_zero]

lemma positive_to_rank_outer_product
    {E : Type*} [Qudit E] (T : L E) (hT : 0 ≤ T) :
    ∃ (κ : Type u) (_ : DecidableEq κ) (_ : Fintype κ),
      Fintype.card κ = Module.finrank ℂ (LinearMap.range T) ∧
        ∃ u : κ → E, T = ∑ a : κ, outer_product (u a) (u a) := by
  let n := Module.finrank ℂ E
  let hTpos : T.IsPositive := (LinearMap.nonneg_iff_isPositive T).mp hT
  let hSym : T.IsSymmetric := hTpos.isSymmetric
  let κ₀ := { i : Fin n // hSym.eigenvalues rfl i ≠ 0 }
  let κ := ULift κ₀
  have hcard₀ : Fintype.card κ₀ = Module.finrank ℂ (LinearMap.range T) := by
    exact card_nonzero_eigenvalues_eq_finrank_range T hT
  have hcard : Fintype.card κ = Module.finrank ℂ (LinearMap.range T) := by
    simpa [κ, Fintype.card_ulift] using hcard₀
  obtain ⟨u₀, hu₀⟩ :=
    positive_spectral_outer_product (T := T) (hT := hT)
  refine ⟨κ, inferInstance, inferInstance, hcard, ?_⟩
  refine ⟨fun a : κ => u₀ a.down, ?_⟩
  have hsum :
      (∑ a : κ, outer_product (u₀ a.down) (u₀ a.down)) =
        ∑ a : κ₀, outer_product (u₀ a) (u₀ a) := by
    symm
    refine Fintype.sum_equiv (Equiv.ulift.symm : κ₀ ≃ κ) _ _ ?_
    intro a
    rfl
  exact hu₀.trans hsum.symm

theorem hasRankKraus_to_hasKraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasRankKraus b Φ → HasKraus Φ := by
  rintro ⟨κ, dec, inst, _, hkraus⟩
  exact ⟨κ, dec, inst, hkraus⟩

theorem rankKraus_to_kraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasRankKraus b Φ → HasKraus Φ :=
  hasRankKraus_to_hasKraus b Φ





noncomputable def conjugateEnd {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (e : E ≃ₗ[ℂ] F) :
    (E →ₗ[ℂ] E) →ₗ[ℂ] (F →ₗ[ℂ] F) where
  toFun X := e.toLinearMap.comp (X.comp e.symm.toLinearMap)
  map_add' X Y := by
    ext x
    simp
  map_smul' c X := by
    ext x
    simp



noncomputable def TrRight {ℋ₃ : Type u} [Qudit ℋ₃] : T (ℋ₂ ⊗[ℂ] ℋ₃) ℋ₂ :=
  (Tr₂ (ℋ₁ := ℋ₃) (ℋ₂ := ℋ₂)).comp
    (conjugateEnd (TensorProduct.comm ℂ ℋ₂ ℋ₃))

noncomputable def krausToStinespringOperator
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) :
    ℋ₁ →ₗ[ℂ] (ℋ₂ ⊗[ℂ] EuclideanSpace ℂ κ) where
  toFun x := ∑ a : κ, (A a x) ⊗ₜ[ℂ] (EuclideanSpace.basisFun κ ℂ a)
  map_add' x y := by
    simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp [TensorProduct.smul_tmul', Finset.smul_sum]

lemma krausToStinespringOperator_apply
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) (x : ℋ₁) :
    krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A x
      = ∑ a : κ, (A a x) ⊗ₜ[ℂ] (EuclideanSpace.basisFun κ ℂ a) :=
  rfl

lemma adjoint_krausToStinespringOperator_tmul_basisFun
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) (y : ℋ₂) (b : κ) :
    (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A))
        (y ⊗ₜ[ℂ] EuclideanSpace.basisFun κ ℂ b) =
      (LinearMap.adjoint (A b)) y := by
  apply ext_inner_right ℂ
  intro x
  rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
  simp [krausToStinespringOperator_apply, inner_sum, TensorProduct.inner_tmul,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

lemma conjugateEnd_krausToStinespringOperator_apply_basisFun_tmul
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) (X : L ℋ₁) (b : κ) (y : ℋ₂) :
    (conjugateEnd (TensorProduct.comm ℂ ℋ₂ (EuclideanSpace ℂ κ))
        (((krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A).comp X).comp
          (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A))))
      ((EuclideanSpace.basisFun κ ℂ b) ⊗ₜ[ℂ] y) =
        ∑ a : κ, (EuclideanSpace.basisFun κ ℂ a) ⊗ₜ[ℂ]
          ((A a).comp (X.comp (LinearMap.adjoint (A b))) y) := by
  have hadj :
      (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A))
          (y ⊗ₜ[ℂ] EuclideanSpace.single b (1 : ℂ)) =
        (LinearMap.adjoint (A b)) y := by
    simpa [EuclideanSpace.basisFun_apply] using
      (adjoint_krausToStinespringOperator_tmul_basisFun
        (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) (κ := κ) A y b)
  simp [conjugateEnd, krausToStinespringOperator_apply, LinearMap.comp_apply,
    EuclideanSpace.basisFun_apply, hadj]

lemma conjugateEnd_krausToStinespringOperator_apply_single_tmul
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) (X : L ℋ₁) (b : κ) (y : ℋ₂) :
    (conjugateEnd (TensorProduct.comm ℂ ℋ₂ (EuclideanSpace ℂ κ))
        (((krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A).comp X).comp
          (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A))))
      ((EuclideanSpace.single b (1 : ℂ)) ⊗ₜ[ℂ] y) =
        ∑ a : κ, (EuclideanSpace.single a (1 : ℂ)) ⊗ₜ[ℂ]
          ((A a).comp (X.comp (LinearMap.adjoint (A b))) y) := by
  simpa [EuclideanSpace.basisFun_apply] using
    (conjugateEnd_krausToStinespringOperator_apply_basisFun_tmul
      (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A X b y)

lemma finrank_kraus_environment
    {κ : Type u} [DecidableEq κ] [Fintype κ] :
    Module.finrank ℂ (EuclideanSpace ℂ κ) = Fintype.card κ := by
  simp [finrank_euclideanSpace (𝕜 := ℂ) (ι := κ)]

lemma linearMap_eq_sum_outer_product
    {E : Type u} [Qudit E] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) (T : L E) :
    T = ∑ i : ι, outer_product (b i) (T (b i)) := by
  ext x
  have hsum : T x = ∑ i : ι, inner ℂ (b i) x • T (b i) := by
    simpa using congrArg T (b.sum_repr' x).symm
  calc
    T x = ∑ i : ι, inner ℂ (b i) x • T (b i) := hsum
    _ = (∑ i : ι, outer_product (b i) (T (b i))) x := by
      simp [LinearMap.sum_apply, outer_product_eq_rankOne]

lemma basis_dual_inner
    {E : Type u} [Qudit E] {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι ℂ E) (i j : ι) :
    inner ℂ (b i)
      ((InnerProductSpace.toDual ℂ E).symm ((b.coord j).toContinuousLinearMap)) =
        if i = j then 1 else 0 := by
  rw [← inner_conj_symm]
  have h :
      inner ℂ
        ((InnerProductSpace.toDual ℂ E).symm ((b.coord j).toContinuousLinearMap))
        (b i) = if i = j then 1 else 0 := by
    simpa using (Module.Basis.dualBasis_apply_self b j i)
  rw [h]
  by_cases hij : i = j <;> simp [hij]

lemma basis_sum_dual
    {E : Type u} [Qudit E] {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι ℂ E) (x : E) :
    x =
      ∑ i : ι, inner ℂ (b i) x •
        ((InnerProductSpace.toDual ℂ E).symm ((b.coord i).toContinuousLinearMap)) := by
  apply InnerProductSpace.ext_inner_left_basis b
  intro j
  rw [inner_sum]
  simp [inner_smul_right, basis_dual_inner]

lemma linearMap_eq_sum_basis_outer_product
    {E : Type u} [Qudit E] {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι ℂ E) (T : L E) :
    T =
      ∑ i : ι, ∑ j : ι,
        (b.coord j
          (T ((InnerProductSpace.toDual ℂ E).symm ((b.coord i).toContinuousLinearMap)))) •
          outer_product (b i) (b j) := by
  ext x
  have hx := basis_sum_dual b x
  calc
    T x =
        T (∑ i : ι, inner ℂ (b i) x •
          ((InnerProductSpace.toDual ℂ E).symm ((b.coord i).toContinuousLinearMap))) := by
          rw [← hx]
    _ = ∑ i : ι, inner ℂ (b i) x •
          T ((InnerProductSpace.toDual ℂ E).symm ((b.coord i).toContinuousLinearMap)) := by
          simp [map_sum]
    _ = ∑ i : ι, inner ℂ (b i) x •
          (∑ j : ι,
            (b.coord j
              (T ((InnerProductSpace.toDual ℂ E).symm ((b.coord i).toContinuousLinearMap)))) •
              b j) := by
          simp [b.sum_repr]
    _ = (∑ i : ι, ∑ j : ι,
        (b.coord j
          (T ((InnerProductSpace.toDual ℂ E).symm ((b.coord i).toContinuousLinearMap)))) •
          outer_product (b i) (b j)) x := by
          simp only [LinearMap.sum_apply]
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl ?_
          intro j _
          simp [outer_product, dualTensorHom_apply, smul_smul, mul_comm]

lemma basis_outer_coeff
    {E : Type u} [Qudit E] {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι ℂ E) (p q i j : ι) :
    b.coord q ((outer_product (b i) (b j))
      ((InnerProductSpace.toDual ℂ E).symm ((b.coord p).toContinuousLinearMap))) =
        if i = p then if j = q then 1 else 0 else 0 := by
  have hinner := basis_dual_inner b i p
  by_cases hip : i = p
  · subst hip
    by_cases hjq : j = q <;> simp [outer_product, dualTensorHom_apply, hinner, hjq]
  · simp [outer_product, dualTensorHom_apply, hinner, hip]

lemma l_tensor_equiv_symm_outer_product
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (u v : E) (x y : F) :
    (l_tensor_equiv (ℋ₁ := E) (ℋ₂ := F)).symm
      ((outer_product u v) ⊗ₜ[ℂ] (outer_product x y)) =
        outer_product (u ⊗ₜ[ℂ] x) (v ⊗ₜ[ℂ] y) := by
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro a b
    simp [l_tensor_equiv, outer_product, TensorProduct.inner_tmul, smul_tmul']
  · intro z₁ z₂ hz₁ hz₂
    simp [hz₁, hz₂]
end RepresentationsOfChannels
end QuantumChannel


