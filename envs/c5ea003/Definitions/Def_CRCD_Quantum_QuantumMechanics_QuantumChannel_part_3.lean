-- Prove2me | Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumChannel_part_3
-- name    : CRCD_Quantum_QuantumMechanics_QuantumChannel_part_3
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T23:49:48.782509+00:00
-- url     : https://prove2.me/theorems/4201bb11-0cb5-402f-9e73-98e4b79d486e
-- title:
--   Choi reconstruction, partial-trace Kraus sums, and Stinespring representation predicates
-- statement:
--   For finite-dimensional complex Hilbert spaces $H_1,H_2$, a finite input basis $b$, and a superoperator $\Phi:\mathcal L(H_1)\to\mathcal L(H_2)$, this part proves that $\Phi\mapsto C_b(\Phi)$ is injective and relates Choi outer-product decompositions to Kraus representations. In particular, a finite Kraus family satisfies
--   $$
--   C_b\!\left(X\mapsto\sum_a A_aXA_a^*\right)
--    =\sum_a |\operatorname{vec}_b(A_a)\rangle\langle\operatorname{vec}_b(A_a)|,
--   $$
--   and a finite decomposition of $C_b(\Phi)$ into positive rank-one terms yields a Kraus representation of $\Phi$. Positivity of the Choi operator therefore yields a representation with exactly $\operatorname{rank}C_b(\Phi)$ Kraus terms. Positivity of the tensor amplification yields Choi positivity; complete positivity yields that amplification positivity.
--
--   For finite-dimensional complex Hilbert spaces $E,F$ and an orthonormal basis $(e_i)$ of $F$, define the right slice $S_i:E\otimes F\to E$ by $S_i(x\otimes y)=\langle e_i,y\rangle x$. The new partial-trace formula is
--   $$
--   \mathrm{Tr}_{\mathrm{right}}(X)=\sum_i S_iXS_i^*,\qquad X\in\mathcal L(E\otimes F).
--   $$
--   It entails complete positivity of the right partial trace and formulas for its action on outer products. Composition of completely positive superoperators is also proved completely positive.
--
--   A Stinespring representation is defined by the existence of a finite-dimensional complex environment $F$ and a linear operator $W:H_1\to H_2\otimes F$ satisfying
--   $$
--   \Phi(X)=\mathrm{Tr}_{\mathrm{right}}(WXW^*)\quad\text{for every }X.
--   $$
--   The rank-sized version additionally requires $\dim_{\mathbb C}F=\operatorname{rank}C_b(\Phi)$. The part supplies the implications that forget this dimension equality and constructs a Stinespring representation from a finite Kraus representation using the previously defined dilation operator. The representation predicates concern general completely positive maps; they do not assert trace preservation or that $W$ is an isometry.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumMechanics/QuantumChannel.lean#L1633-L2348

import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumChannel_part_2
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























































































































































































lemma l_tensor_equiv_outer_product_tmul
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (u v : E) (x y : F) :
    (l_tensor_equiv (ℋ₁ := E) (ℋ₂ := F))
      (outer_product (u ⊗ₜ[ℂ] x) (v ⊗ₜ[ℂ] y)) =
        (outer_product u v) ⊗ₜ[ℂ] (outer_product x y) := by
  apply (l_tensor_equiv (ℋ₁ := E) (ℋ₂ := F)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (l_tensor_equiv_symm_outer_product (E := E) (F := F) u v x y).symm

lemma choi_basis_expansion
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    choi b Φ =
      ∑ i : ι, ∑ j : ι,
        (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
          ((Φ (outer_product (b i) (b j))) ⊗ₜ[ℂ] outer_product (b i) (b j)) := by
  rw [choi, vec_apply]
  simp only [I, LinearMap.id_coe, id_eq]
  change (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
      ((TensorProduct.map Φ LinearMap.id)
        ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁))
          (outer_product (∑ i : ι, b i ⊗ₜ[ℂ] b i) (∑ i : ι, b i ⊗ₜ[ℂ] b i)))) =
    ∑ i : ι, ∑ j : ι,
      (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
        ((Φ (outer_product (b i) (b j))) ⊗ₜ[ℂ] outer_product (b i) (b j))
  rw [show outer_product (∑ i : ι, b i ⊗ₜ[ℂ] b i) (∑ i : ι, b i ⊗ₜ[ℂ] b i) =
      ∑ i : ι, ∑ j : ι, outer_product (b i ⊗ₜ[ℂ] b i) (b j ⊗ₜ[ℂ] b j) by
    exact outer_product_sum (fun i : ι => b i ⊗ₜ[ℂ] b i) (fun i : ι => b i ⊗ₜ[ℂ] b i)]
  simp only [map_sum]
  simp_rw [l_tensor_equiv_outer_product_tmul]
  simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq]

lemma tensor_basis_sum_coeff
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι ℂ E) (p q : ι) (S : ι → ι → L F) :
    (TensorProduct.rid ℂ (L F)).toLinearMap
      ((TensorProduct.map LinearMap.id
        { toFun := fun X : L E =>
            b.coord q (X ((InnerProductSpace.toDual ℂ E).symm ((b.coord p).toContinuousLinearMap)))
          map_add' := by intro X Y; simp
          map_smul' := by intro c X; simp })
        (∑ i : ι, ∑ j : ι, S i j ⊗ₜ[ℂ] outer_product (b i) (b j))) =
      S p q := by
  classical
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · have hcoeff :
          (b.repr ((outer_product (b p) (b q))
            ((InnerProductSpace.toDual ℂ E).symm
              (LinearMap.toContinuousLinearMap (b.coord p))))) q = 1 := by
          simpa using (basis_outer_coeff b p q p q)
      simp [Module.Basis.coord_apply, hcoeff]
    · intro j _ hjq
      have hcoeff :
          (b.repr ((outer_product (b p) (b j))
            ((InnerProductSpace.toDual ℂ E).symm
              (LinearMap.toContinuousLinearMap (b.coord p))))) q = 0 := by
          simpa [hjq] using (basis_outer_coeff b p q p j)
      simp [Module.Basis.coord_apply, hcoeff]
    · intro hq
      simp at hq
  · intro i _ hip
    apply Finset.sum_eq_zero
    intro j _
    have hcoeff :
        (b.repr ((outer_product (b i) (b j))
          ((InnerProductSpace.toDual ℂ E).symm
            (LinearMap.toContinuousLinearMap (b.coord p))))) q = 0 := by
        simpa [hip] using (basis_outer_coeff b p q i j)
    simp [Module.Basis.coord_apply, hcoeff]
  · intro hp
    simp at hp

lemma choi_basis_apply_eq_of_choi_eq
    (b : Module.Basis ι ℂ ℋ₁) {Φ Ψ : T ℋ₁ ℋ₂}
    (h : choi b Φ = choi b Ψ) (i j : ι) :
    Φ (outer_product (b i) (b j)) = Ψ (outer_product (b i) (b j)) := by
  have htensor :
      (∑ p : ι, ∑ q : ι,
        Φ (outer_product (b p) (b q)) ⊗ₜ[ℂ] outer_product (b p) (b q)) =
      (∑ p : ι, ∑ q : ι,
        Ψ (outer_product (b p) (b q)) ⊗ₜ[ℂ] outer_product (b p) (b q)) := by
    have h' := congrArg (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)) h
    simpa [choi_basis_expansion] using h'
  calc
    Φ (outer_product (b i) (b j)) =
        (TensorProduct.rid ℂ (L ℋ₂)).toLinearMap
          ((TensorProduct.map LinearMap.id
            { toFun := fun X : L ℋ₁ =>
                b.coord j
                  (X ((InnerProductSpace.toDual ℂ ℋ₁).symm ((b.coord i).toContinuousLinearMap)))
              map_add' := by intro X Y; simp
              map_smul' := by intro c X; simp })
            (∑ p : ι, ∑ q : ι,
              Φ (outer_product (b p) (b q)) ⊗ₜ[ℂ] outer_product (b p) (b q))) := by
          exact (tensor_basis_sum_coeff b i j
            (fun p q => Φ (outer_product (b p) (b q)))).symm
    _ =
        (TensorProduct.rid ℂ (L ℋ₂)).toLinearMap
          ((TensorProduct.map LinearMap.id
            { toFun := fun X : L ℋ₁ =>
                b.coord j
                  (X ((InnerProductSpace.toDual ℂ ℋ₁).symm ((b.coord i).toContinuousLinearMap)))
              map_add' := by intro X Y; simp
              map_smul' := by intro c X; simp })
            (∑ p : ι, ∑ q : ι,
              Ψ (outer_product (b p) (b q)) ⊗ₜ[ℂ] outer_product (b p) (b q))) := by
          rw [htensor]
    _ = Ψ (outer_product (b i) (b j)) := by
          exact tensor_basis_sum_coeff b i j
            (fun p q => Ψ (outer_product (b p) (b q)))

lemma choi_injective
    (b : Module.Basis ι ℂ ℋ₁) :
    Function.Injective (choi b : T ℋ₁ ℋ₂ → L (ℋ₂ ⊗[ℂ] ℋ₁)) := by
  intro Φ Ψ h
  apply LinearMap.ext
  intro X
  conv_lhs => rw [linearMap_eq_sum_basis_outer_product b X]
  conv_rhs => rw [linearMap_eq_sum_basis_outer_product b X]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [choi_basis_apply_eq_of_choi_eq b h i j]

lemma outer_product_vec_expansion
    (b : Module.Basis ι ℂ ℋ₁) (A : ℋ₁ →ₗ[ℂ] ℋ₂) :
    outer_product (vec b A) (vec b A) =
      ∑ i : ι, ∑ j : ι,
        (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
          ((outer_product (A (b i)) (A (b j))) ⊗ₜ[ℂ] outer_product (b i) (b j)) := by
  rw [vec_apply]
  rw [show outer_product (∑ i : ι, A (b i) ⊗ₜ[ℂ] b i)
      (∑ i : ι, A (b i) ⊗ₜ[ℂ] b i) =
      ∑ i : ι, ∑ j : ι,
        outer_product (A (b i) ⊗ₜ[ℂ] b i) (A (b j) ⊗ₜ[ℂ] b j) by
    exact outer_product_sum
      (fun i : ι => A (b i) ⊗ₜ[ℂ] b i)
      (fun i : ι => A (b i) ⊗ₜ[ℂ] b i)]
  simp_rw [← l_tensor_equiv_symm_outer_product]

lemma choi_kraus_expansion
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis ι ℂ ℋ₁) (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) :
    choi b
      { toFun := fun X => ∑ a : κ, (A a).comp (X.comp (LinearMap.adjoint (A a)))
        map_add' := by
          intro X Y
          simp [LinearMap.comp_add, LinearMap.add_comp, Finset.sum_add_distrib]
        map_smul' := by
          intro c X
          simp [LinearMap.comp_smul, LinearMap.smul_comp, Finset.smul_sum] } =
      ∑ a : κ, outer_product (vec b (A a)) (vec b (A a)) := by
  classical
  rw [choi_basis_expansion]
  change
    ∑ i : ι, ∑ j : ι,
      (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
        (((∑ a : κ, (A a).comp ((outer_product (b i) (b j)).comp
          (LinearMap.adjoint (A a)))) ⊗ₜ[ℂ] outer_product (b i) (b j))) =
      ∑ a : κ, outer_product (vec b (A a)) (vec b (A a))
  simp_rw [comp_outer_product_adjoint]
  simp_rw [TensorProduct.sum_tmul]
  simp only [map_sum]
  simp_rw [outer_product_vec_expansion]
  let F : ι → ι → κ → L (ℋ₂ ⊗[ℂ] ℋ₁) :=
    fun i j a =>
      (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
        ((outer_product (A a (b i)) (A a (b j))) ⊗ₜ[ℂ] outer_product (b i) (b j))
  change ∑ i : ι, ∑ j : ι, ∑ a : κ, F i j a =
    ∑ a : κ, ∑ i : ι, ∑ j : ι, F i j a
  calc
    ∑ i : ι, ∑ j : ι, ∑ a : κ, F i j a
        = ∑ i : ι, ∑ a : κ, ∑ j : ι, F i j a := by
          refine Finset.sum_congr rfl ?_
          intro i _
          exact Finset.sum_comm
    _ = ∑ a : κ, ∑ i : ι, ∑ j : ι, F i j a := by
          exact Finset.sum_comm

lemma choi_outer_product_kraus_apply
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂)
    (u : κ → ℋ₂ ⊗[ℂ] ℋ₁)
    (hΦ : choi b Φ = ∑ a : κ, outer_product (u a) (u a))
    (X : L ℋ₁) :
    let A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂) :=
      fun a => (vecLinearEquiv (ℋ₁ := ℋ₂) b).symm (u a)
    Φ X = ∑ a : κ, (A a).comp (X.comp (LinearMap.adjoint (A a))) := by
  classical
  let A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂) :=
    fun a => (vecLinearEquiv (ℋ₁ := ℋ₂) b).symm (u a)
  let Ψ : T ℋ₁ ℋ₂ :=
    { toFun := fun X => ∑ a : κ, (A a).comp (X.comp (LinearMap.adjoint (A a)))
      map_add' := by
        intro X Y
        simp [LinearMap.comp_add, LinearMap.add_comp, Finset.sum_add_distrib]
      map_smul' := by
        intro c X
        simp [LinearMap.comp_smul, LinearMap.smul_comp, Finset.smul_sum] }
  have hvec : ∀ a : κ, vec b (A a) = u a := by
    intro a
    rw [← vecLinearEquiv_toLinearMap (ℋ₁ := ℋ₂) b]
    exact LinearEquiv.apply_symm_apply (vecLinearEquiv (ℋ₁ := ℋ₂) b) (u a)
  have hΨ : choi b Ψ = choi b Φ := by
    rw [choi_kraus_expansion]
    simp_rw [hvec]
    exact hΦ.symm
  have hmap : Ψ = Φ := choi_injective b hΨ
  change Φ X = Ψ X
  exact (LinearMap.congr_fun hmap X).symm

lemma choi_outer_product_to_kraus
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂)
    (u : κ → ℋ₂ ⊗[ℂ] ℋ₁)
    (hΦ : choi b Φ = ∑ a : κ, outer_product (u a) (u a)) :
    KrausRep Φ κ := by
  refine ⟨fun a => (vecLinearEquiv (ℋ₁ := ℋ₂) b).symm (u a), ?_⟩
  intro X
  exact choi_outer_product_kraus_apply b Φ u hΦ X







set_option linter.flexible false in
lemma l_tensor_equiv_symm_outer_product_apply
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (u v x : E) (T : L F) (y : F) :
    ((l_tensor_equiv (ℋ₁ := E) (ℋ₂ := F)).symm
      ((outer_product u v) ⊗ₜ[ℂ] T)) (x ⊗ₜ[ℂ] y) =
        (outer_product u v x) ⊗ₜ[ℂ] T y := by
  let b := stdOrthonormalBasis ℂ F
  rw [linearMap_eq_sum_outer_product b T]
  rw [TensorProduct.tmul_sum]
  rw [map_sum]
  simp only [LinearMap.sum_apply, l_tensor_equiv_symm_outer_product]
  simp [outer_product_eq_rankOne, TensorProduct.inner_tmul]
  rw [TensorProduct.tmul_sum]
  simp [smul_tmul', smul_smul, mul_comm]

lemma ite_tmul_zero_left
    {E : Type u} {F : Type v}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (p : Prop) [Decidable p] (x : E) (y : F) :
    (if p then x else 0) ⊗ₜ[ℂ] y = if p then x ⊗ₜ[ℂ] y else 0 := by
  by_cases hp : p <;> simp [hp]

lemma trace_outer_product_basisFun
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (a b : κ) :
    Tr (outer_product (EuclideanSpace.basisFun κ ℂ a) (EuclideanSpace.basisFun κ ℂ b)) =
      if a = b then 1 else 0 := by
  rw [outer_product_eq_rankOne, InnerProductSpace.trace_rankOne]
  by_cases hab : a = b
  · subst hab
    simp [EuclideanSpace.basisFun_apply]
  · simpa [hab] using (EuclideanSpace.basisFun κ ℂ).inner_eq_ite a b

lemma trace_outer_product_single
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (a b : κ) :
    Tr (outer_product (EuclideanSpace.single a (1 : ℂ)) (EuclideanSpace.single b (1 : ℂ))) =
      if a = b then 1 else 0 := by
  simpa [EuclideanSpace.basisFun_apply] using
    (trace_outer_product_basisFun (κ := κ) a b)

lemma trace_outer_product
    {E : Type u} [Qudit E] (u v : E) :
    Tr (outer_product u v) = inner ℂ u v := by
  rw [outer_product_eq_rankOne]
  simpa using InnerProductSpace.trace_rankOne (𝕜 := ℂ) (E := E) v u

noncomputable def tensorRightSlice
    {κ : Type*} [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (i : κ) :
    E ⊗[ℂ] F →ₗ[ℂ] E :=
  (TensorProduct.rid ℂ E).toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (b.toBasis.coord i)

lemma tensorRightSlice_tmul
    {κ : Type*} [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (i : κ) (x : E) (y : F) :
    tensorRightSlice (E := E) (F := F) b i (x ⊗ₜ[ℂ] y) =
      b.toBasis.coord i y • x := by
  simp [tensorRightSlice]

lemma tensorRightSlice_expand
    {κ : Type*} [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (z : E ⊗[ℂ] F) :
    z = ∑ i : κ, tensorRightSlice (E := E) (F := F) b i z ⊗ₜ[ℂ] b i := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro x y
    calc
      x ⊗ₜ[ℂ] y = x ⊗ₜ[ℂ] (∑ i : κ, b.repr y i • b i) := by
        rw [b.sum_repr]
      _ = ∑ i : κ, x ⊗ₜ[ℂ] (b.repr y i • b i) := by
        rw [TensorProduct.tmul_sum]
      _ = ∑ i : κ, (b.toBasis.coord i y • x) ⊗ₜ[ℂ] b i := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        simp [OrthonormalBasis.repr_apply_apply]
  · intro x y hx hy
    calc
      x + y =
          ∑ i, (tensorRightSlice (E := E) (F := F) b i) x ⊗ₜ[ℂ] b i +
            ∑ i, (tensorRightSlice (E := E) (F := F) b i) y ⊗ₜ[ℂ] b i := by
            exact congrArg₂ (fun a b => a + b) hx hy
      _ =
          ∑ i,
            ((tensorRightSlice (E := E) (F := F) b i) x ⊗ₜ[ℂ] b i +
              (tensorRightSlice (E := E) (F := F) b i) y ⊗ₜ[ℂ] b i) := by
            rw [Finset.sum_add_distrib]
      _ =
          ∑ i,
            ((tensorRightSlice (E := E) (F := F) b i) x +
              (tensorRightSlice (E := E) (F := F) b i) y) ⊗ₜ[ℂ] b i := by
            simp [TensorProduct.add_tmul]
      _ =
          ∑ i, (tensorRightSlice (E := E) (F := F) b i) (x + y) ⊗ₜ[ℂ] b i := by
            simp [map_add]

lemma TrRight_outer_product_tmul_basis
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (i j : κ) (x y : E) :
    TrRight (ℋ₂ := E) (ℋ₃ := F)
      (outer_product (x ⊗ₜ[ℂ] b i) (y ⊗ₜ[ℂ] b j)) =
        if i = j then outer_product x y else 0 := by
  dsimp [TrRight]
  have hconj :
      conjugateEnd (TensorProduct.comm ℂ E F)
        (outer_product (x ⊗ₜ[ℂ] b i) (y ⊗ₜ[ℂ] b j)) =
        outer_product (b i ⊗ₜ[ℂ] x) (b j ⊗ₜ[ℂ] y) := by
    apply LinearMap.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [conjugateEnd, outer_product]
    · intro a c
      simp [conjugateEnd, outer_product_eq_rankOne, TensorProduct.inner_tmul, mul_comm]
    · intro z w hz hw
      simp [hz, hw]
  rw [hconj]
  rw [← l_tensor_equiv_symm_outer_product (E := F) (F := E) (b i) (b j) x y]
  rw [Tr₂_l_tensor_equiv_symm_tmul]
  rw [trace_outer_product]
  by_cases hij : i = j
  · subst j
    simp
  · simp [b.inner_eq_ite, hij]

lemma TrRight_outer_product
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (u v : E ⊗[ℂ] F) :
    TrRight (ℋ₂ := E) (ℋ₃ := F) (outer_product u v) =
      ∑ i : κ,
        outer_product
          (tensorRightSlice (E := E) (F := F) b i u)
          (tensorRightSlice (E := E) (F := F) b i v) := by
  conv_lhs =>
    rw [tensorRightSlice_expand (E := E) (F := F) b u,
      tensorRightSlice_expand (E := E) (F := F) b v]
    rw [outer_product_sum]
  simp only [map_sum]
  classical
  calc
    ∑ a : κ, ∑ b' : κ,
        TrRight (ℋ₂ := E) (ℋ₃ := F)
          (outer_product
            (tensorRightSlice (E := E) (F := F) b a u ⊗ₜ[ℂ] b a)
            (tensorRightSlice (E := E) (F := F) b b' v ⊗ₜ[ℂ] b b')) =
      ∑ a : κ, ∑ b' : κ,
        (if a = b' then
          outer_product
            (tensorRightSlice (E := E) (F := F) b a u)
            (tensorRightSlice (E := E) (F := F) b b' v)
        else 0) := by
        refine Finset.sum_congr rfl ?_
        intro a _
        refine Finset.sum_congr rfl ?_
        intro b' _
        exact TrRight_outer_product_tmul_basis (E := E) (F := F) b a b'
          (tensorRightSlice (E := E) (F := F) b a u)
          (tensorRightSlice (E := E) (F := F) b b' v)
    _ =
      ∑ i : κ,
        outer_product
          (tensorRightSlice (E := E) (F := F) b i u)
          (tensorRightSlice (E := E) (F := F) b i v) := by
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [Finset.sum_eq_single a]
        · simp
        · intro b' _ hb'
          have hab : a ≠ b' := fun h => hb' h.symm
          simp [hab]
        · simp

lemma tensorRightSlice_comp_outer_product
    {κ : Type*} [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (i : κ) (u v : E ⊗[ℂ] F) :
    (tensorRightSlice (E := E) (F := F) b i).comp
        ((outer_product u v).comp
          (LinearMap.adjoint (tensorRightSlice (E := E) (F := F) b i))) =
      outer_product
        (tensorRightSlice (E := E) (F := F) b i u)
        (tensorRightSlice (E := E) (F := F) b i v) := by
  exact @comp_outer_product_adjoint (E ⊗[ℂ] F) inferInstance E inferInstance
    (tensorRightSlice (E := E) (F := F) b i) u v

lemma TrRight_eq_kraus_sum
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (X : L (E ⊗[ℂ] F)) :
    TrRight (ℋ₂ := E) (ℋ₃ := F) X =
      (∑ i : κ,
        (tensorRightSlice (E := E) (F := F) b i).comp
          (X.comp (LinearMap.adjoint (tensorRightSlice (E := E) (F := F) b i))) : L E) := by
  let c : OrthonormalBasis (Fin (Module.finrank ℂ (E ⊗[ℂ] F))) ℂ (E ⊗[ℂ] F) :=
    stdOrthonormalBasis ℂ (E ⊗[ℂ] F)
  rw [linearMap_eq_sum_outer_product c X]
  calc
    TrRight (ℋ₂ := E) (ℋ₃ := F) (∑ a, outer_product (c a) (X (c a))) =
        ∑ a, TrRight (ℋ₂ := E) (ℋ₃ := F) (outer_product (c a) (X (c a))) := by
          simp
    _ =
        ∑ a, ∑ i : κ,
          (outer_product
            (tensorRightSlice (E := E) (F := F) b i (c a))
            (tensorRightSlice (E := E) (F := F) b i (X (c a))) : L E) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          exact TrRight_outer_product (E := E) (F := F) b (c a) (X (c a))
    _ =
        ∑ i : κ, ∑ a,
          (outer_product
            (tensorRightSlice (E := E) (F := F) b i (c a))
            (tensorRightSlice (E := E) (F := F) b i (X (c a))) : L E) := by
          rw [Finset.sum_comm]
    _ =
        (∑ i : κ,
          (tensorRightSlice (E := E) (F := F) b i).comp
            ((∑ a, outer_product (c a) (X (c a))).comp
              (LinearMap.adjoint (tensorRightSlice (E := E) (F := F) b i))) : L E) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          calc
            (∑ a,
              (outer_product
                (tensorRightSlice (E := E) (F := F) b i (c a))
                (tensorRightSlice (E := E) (F := F) b i (X (c a))) : L E)) =
                ∑ a,
                  (tensorRightSlice (E := E) (F := F) b i).comp
                    ((outer_product (c a) (X (c a))).comp
                      (LinearMap.adjoint (tensorRightSlice (E := E) (F := F) b i))) := by
                refine Finset.sum_congr rfl ?_
                intro a _
                exact (tensorRightSlice_comp_outer_product
                  (E := E) (F := F) b i (c a) (X (c a))).symm
            _ =
                (tensorRightSlice (E := E) (F := F) b i).comp
                  ((∑ a, outer_product (c a) (X (c a))).comp
                    (LinearMap.adjoint (tensorRightSlice (E := E) (F := F) b i))) := by
                ext z
                simp [LinearMap.comp_apply]

theorem TrRight_krausRep
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) :
    KrausRep (ℋ₁ := E ⊗[ℂ] F) (ℋ₂ := E)
      (TrRight (ℋ₂ := E) (ℋ₃ := F)) κ := by
  refine ⟨fun i => tensorRightSlice (E := E) (F := F) b i, ?_⟩
  intro X
  exact TrRight_eq_kraus_sum b X

theorem TrRight_isCompletelyPositive
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) :
    IsCompletelyPositive (TrRight (ℋ₂ := E) (ℋ₃ := F)) := by
  exact fixed_kraus_to_cp
    (ℋ₁ := E ⊗[ℂ] F) (ℋ₂ := E)
    (TrRight (ℋ₂ := E) (ℋ₃ := F))
    (TrRight_krausRep b)

theorem comp_isCompletelyPositive
    {ℋ₃ : Type w} [Qudit ℋ₃]
    (Φ : T ℋ₁ ℋ₂) (Ψ : T ℋ₂ ℋ₃)
    (hΦ : IsCompletelyPositive Φ) (hΨ : IsCompletelyPositive Ψ) :
    IsCompletelyPositive (Ψ.comp Φ) := by
  refine (isCompletelyPositive_iff_cstarMatrix_nonneg (Ψ.comp Φ)).mpr ?_
  intro k M hM
  have hΦM :
      0 ≤ M.map Φ :=
    (isCompletelyPositive_iff_cstarMatrix_nonneg Φ).mp hΦ k M hM
  have hΨM :
      0 ≤ (M.map Φ).map Ψ :=
    (isCompletelyPositive_iff_cstarMatrix_nonneg Ψ).mp hΨ k (M.map Φ) hΦM
  have hmap : (M.map Φ).map Ψ = M.map (Ψ.comp Φ) := by
    ext i j X
    simp [CStarMatrix.map_apply]
  simpa [hmap] using hΨM

def StinespringRep (Φ : T ℋ₁ ℋ₂) (ℋ₃ : Type u) [Qudit ℋ₃] : Prop :=
  ∃ A : ℋ₁ →ₗ[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃),
    ∀ X : L ℋ₁,
      Φ X =
        (@TrRight ℋ₂ inferInstance ℋ₃ inferInstance
          (((A.comp X).comp
            (LinearMap.adjoint A : (ℋ₂ ⊗[ℂ] ℋ₃) →ₗ[ℂ] ℋ₁)) : L (ℋ₂ ⊗[ℂ] ℋ₃)) : L ℋ₂)

def HasStinespring (Φ : T ℋ₁ ℋ₂) : Prop :=
  ∃ (ℋ₃ : Type u) (_ : Qudit ℋ₃), @StinespringRep ℋ₁ ℋ₂ _ _ Φ ℋ₃ _

def HasRankStinespring (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) : Prop :=
  ∃ (ℋ₃ : Type u) (inst : Qudit ℋ₃),
    Module.finrank ℂ ℋ₃ = choiRank b Φ ∧
      @StinespringRep ℋ₁ ℋ₂ _ _ Φ ℋ₃ inst

lemma stinespring_cstarMatrix_nonneg
    {ℋ₃ : Type u} [Qudit ℋ₃]
    (Φ : T ℋ₁ ℋ₂) (hΦ : StinespringRep Φ ℋ₃) :
    ∀ (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) (L ℋ₁)),
      0 ≤ M → 0 ≤ M.map Φ := by
  obtain ⟨A, hA⟩ := hΦ
  let K : T ℋ₁ (ℋ₂ ⊗[ℂ] ℋ₃) := krausTerm A
  have hK : IsCompletelyPositive K := krausTerm_isCompletelyPositive A
  have hTr : IsCompletelyPositive (TrRight (ℋ₂ := ℋ₂) (ℋ₃ := ℋ₃)) := by
    exact TrRight_isCompletelyPositive (stdOrthonormalBasis ℂ ℋ₃)
  have hΦeq : Φ = (TrRight (ℋ₂ := ℋ₂) (ℋ₃ := ℋ₃)).comp K := by
    apply LinearMap.ext
    intro X
    rw [hA X]
    simp [K, krausTerm, LinearMap.comp_assoc]
  have hCP : IsCompletelyPositive Φ := by
    rw [hΦeq]
    exact comp_isCompletelyPositive K (TrRight (ℋ₂ := ℋ₂) (ℋ₃ := ℋ₃)) hK hTr
  exact (isCompletelyPositive_iff_cstarMatrix_nonneg Φ).mp hCP

theorem hasRankStinespring_to_hasStinespring
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasRankStinespring b Φ → HasStinespring Φ := by
  rintro ⟨ℋ₃, inst, _, hstinespring⟩
  exact ⟨ℋ₃, inst, hstinespring⟩

theorem rankStinespring_to_stinespring
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasRankStinespring b Φ → HasStinespring Φ :=
  hasRankStinespring_to_hasStinespring b Φ

theorem tensor_to_choi
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    AmplificationPositive Φ → ChoiPositive b Φ := by
  intro hΦ
  exact hΦ (outer_product (vec b (I ℋ₁)) (vec b (I ℋ₁)))
    (outer_product_self_nonneg (vec b (I ℋ₁)))

-- (1) → (2)
theorem cp_to_tensor
    (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ → AmplificationPositive Φ := by
  exact cp_amplify Φ

-- (3) → (5)
theorem choi_to_rank_kraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    ChoiPositive b Φ → HasRankKraus b Φ := by
  intro hΦ
  obtain ⟨κ, hκ, hκ', hcard, u, hu⟩ :=
    positive_to_rank_outer_product (choi b Φ) hΦ
  letI : DecidableEq κ := hκ
  letI : Fintype κ := hκ'
  refine ⟨κ, hκ, hκ', ?_, ?_⟩
  · exact hcard
  · exact choi_outer_product_to_kraus b Φ u hu










theorem conjugate_kraus_expansion
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) (X : L ℋ₁) :
    conjugateEnd (TensorProduct.comm ℂ ℋ₂ (EuclideanSpace ℂ κ))
      (((krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A).comp X).comp
        (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A))) =
      ∑ a : κ, ∑ b : κ,
        (l_tensor_equiv (ℋ₁ := EuclideanSpace ℂ κ) (ℋ₂ := ℋ₂)).symm
          ((outer_product (EuclideanSpace.basisFun κ ℂ b) (EuclideanSpace.basisFun κ ℂ a)) ⊗ₜ[ℂ]
            ((A a).comp (X.comp (LinearMap.adjoint (A b))))) := by
  classical
  apply TensorProduct.ext'
  intro z y
  rw [← (EuclideanSpace.basisFun κ ℂ).sum_repr' z]
  simp_rw [TensorProduct.sum_tmul]
  simp_rw [← TensorProduct.smul_tmul']
  simp [map_sum, map_smul,
    conjugateEnd_krausToStinespringOperator_apply_single_tmul,
    l_tensor_equiv_symm_outer_product_apply, EuclideanSpace.basisFun_apply]
  simp [outer_product_eq_rankOne, EuclideanSpace.inner_single_left, ite_tmul_zero_left]

theorem trRight_kraus
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) (X : L ℋ₁) :
    TrRight ((((krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A).comp X).comp
      (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A)))) =
      ∑ a : κ, (A a).comp (X.comp (LinearMap.adjoint (A a))) := by
  classical
  dsimp [TrRight]
  rw [conjugate_kraus_expansion (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A X]
  simp [Tr₂_l_tensor_equiv_symm_tmul, trace_outer_product_single, EuclideanSpace.basisFun_apply]


theorem fixed_kraus_to_stinespring
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (Φ : T ℋ₁ ℋ₂) :
    KrausRep Φ κ → StinespringRep Φ (EuclideanSpace ℂ κ) := by
  rintro ⟨A, hA⟩
  refine ⟨krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A, ?_⟩
  intro X
  rw [hA X]
  simpa using (trRight_kraus (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A X).symm

-- (4) → (6)
theorem kraus_to_stinespring
    (Φ : T ℋ₁ ℋ₂) :
    HasKraus Φ → HasStinespring Φ := by
  rintro ⟨κ, hκ, hκ', hΦ⟩
  letI : DecidableEq κ := hκ
  letI : Fintype κ := hκ'
  exact ⟨EuclideanSpace ℂ κ, inferInstance,
    fixed_kraus_to_stinespring (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) Φ hΦ⟩
end RepresentationsOfChannels
end QuantumChannel


