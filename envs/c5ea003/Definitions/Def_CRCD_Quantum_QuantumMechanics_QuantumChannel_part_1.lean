-- Prove2me | Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumChannel_part_1
-- name    : CRCD_Quantum_QuantumMechanics_QuantumChannel_part_1
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T23:45:51.285709+00:00
-- url     : https://prove2.me/theorems/d17ba35d-6277-49f8-b9a6-56ae40a3b4f3
-- title:
--   Finite-dimensional quantum operators, complete positivity, and matrix amplification
-- statement:
--   Let $H_1,H_2$ be finite-dimensional complex Hilbert spaces, possibly of dimension zero, and write $\mathcal L(H)$ for complex-linear endomorphisms and $\operatorname{Tr}$ for the ordinary, unnormalized trace. This part equips these endomorphism spaces with the operator norm, C*-algebra structure and positive-operator order, transported from bounded operators, and defines superoperators $\Phi:\mathcal L(H_1)\to\mathcal L(H_2)$. A CPTP map is a completely positive superoperator satisfying $\operatorname{Tr}\Phi(X)=\operatorname{Tr}X$ for every operator $X$; positivity and $k$-positivity mean preservation of positive operators and of positive $k\times k$ operator matrices, respectively. Complete positivity is expressed by a Mathlib completely positive map with underlying linear map $\Phi$, equivalently positivity of every finite matrix amplification.
--
--   The tensor-operator identification sends $X\otimes Y$ to its natural action on $H_1\otimes H_2$. The partial trace denoted $\mathrm{Tr}_2$ in this source traces the first tensor factor:
--   $$
--   \mathrm{Tr}_2(X\otimes Y)=\operatorname{Tr}(X)Y.
--   $$
--   For a finite input basis $b=(b_i)$, vectorization and the basis-dependent Choi operator are
--   $$
--   \operatorname{vec}_b(V)=\sum_i Vb_i\otimes b_i,\qquad
--   C_b(\Phi)=(\Phi\otimes\mathrm{id})\bigl(|\Omega_b\rangle\langle\Omega_b|\bigr),\qquad
--   \Omega_b=\sum_i b_i\otimes b_i.
--   $$
--   Here the source's $\operatorname{outer\_product}(u,v)$ means $|v\rangle\langle u|$, namely $x\mapsto\langle u,x\rangle v$, with the inner product conjugate-linear in its first argument. For an orthonormal basis, vectorization satisfies $\langle\operatorname{vec}_b(A),\operatorname{vec}_b(B)\rangle=\operatorname{Tr}(A^*B)$. The remaining new interfaces identify operators on the Hilbert direct sum of $k$ copies of $H$ with C*-operator matrices, realize entrywise amplification on that direct sum, and supply coordinate inclusions, projections and the componentwise amplification of a linear map $V$. The Kraus term $X\mapsto VXV^*$ is proved positive at this stage.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumMechanics/QuantumChannel.lean#L30-L946

import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
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
abbrev T (ℋ₁ : Type u) (ℋ₂ : Type v)
  [AddCommGroup ℋ₁] [Module ℂ ℋ₁] [AddCommGroup ℋ₂] [Module ℂ ℋ₂] : Type (max u v) :=
  (L ℋ₁) →ₗ[ℂ] (L ℋ₂)

section ContinuousLinearMapsAreCStarAlgebras

noncomputable instance continuous_instance {ℋ : Type u} [Qudit ℋ] : CStarAlgebra (ℋ →L[ℂ] ℋ)
  := inferInstance

noncomputable instance (ℋ : Type u) [Qudit ℋ] : Norm (L ℋ) where
  norm := fun X => ‖X.toContinuousLinearMap‖

noncomputable instance (ℋ : Type u) [Qudit ℋ] : MetricSpace (L ℋ) :=
  MetricSpace.induced LinearMap.toContinuousLinearMap
    LinearMap.toContinuousLinearMap.injective inferInstance

noncomputable instance linear_isometry_equiv {ℋ : Type u} [Qudit ℋ] : (L ℋ) ≃ᵢ (ℋ →L[ℂ] ℋ) where
  toFun := fun X => X.toContinuousLinearMap
  invFun := fun X => X.toLinearMap
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  isometry_toFun := fun _ _ => rfl

noncomputable instance c_algebra_instance {ℋ : Type u} [Qudit ℋ] : Algebra ℂ (L ℋ) := inferInstance

noncomputable instance (ℋ : Type u) [Qudit ℋ] : CStarAlgebra (L ℋ) where
  dist_eq x y := continuous_instance.dist_eq x.toContinuousLinearMap y.toContinuousLinearMap
  norm_mul_le x y := continuous_instance.norm_mul_le x.toContinuousLinearMap y.toContinuousLinearMap
  complete := (linear_isometry_equiv.completeSpace_iff.mpr
    continuous_instance.toCompleteSpace).complete
  norm_mul_self_le x := continuous_instance.norm_mul_self_le x.toContinuousLinearMap
  algebraMap := c_algebra_instance.algebraMap
  commutes' := c_algebra_instance.commutes'
  smul_def' := c_algebra_instance.smul_def'
  norm_smul_le r x := continuous_instance.norm_smul_le r x.toContinuousLinearMap

noncomputable instance continuous_sor_instance {ℋ : Type u} [Qudit ℋ] : StarOrderedRing (ℋ →L[ℂ] ℋ)
  := inferInstance

 lemma closure_clm_of_closure_lm {ℋ : Type u} [Qudit ℋ]
    {p : L ℋ} (hp : p ∈ AddSubmonoid.closure (Set.range fun s : L ℋ ↦ star s * s)) :
    p.toContinuousLinearMap ∈
      AddSubmonoid.closure (Set.range fun s : ℋ →L[ℂ] ℋ ↦ star s * s) := by
  induction hp using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨s, hs⟩ := hx
    exact AddSubmonoid.subset_closure ⟨s.toContinuousLinearMap, by subst hs; rfl⟩
  | zero => exact AddSubmonoid.zero_mem _
  | add x y _ _ ihx ihy => exact AddSubmonoid.add_mem _ ihx ihy

 lemma closure_lm_of_closure_clm {ℋ : Type u} [Qudit ℋ]
    {p : ℋ →L[ℂ] ℋ} (hp : p ∈ AddSubmonoid.closure (Set.range fun s : ℋ →L[ℂ] ℋ ↦ star s * s)) :
    p.toLinearMap ∈
      AddSubmonoid.closure (Set.range fun s : L ℋ ↦ star s * s) := by
  induction hp using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨s, hs⟩ := hx
    exact AddSubmonoid.subset_closure ⟨s.toLinearMap, by subst hs; rfl⟩
  | zero => exact AddSubmonoid.zero_mem _
  | add x y _ _ ihx ihy => exact AddSubmonoid.add_mem _ ihx ihy

noncomputable instance (ℋ : Type u) [Qudit ℋ] : StarOrderedRing (L ℋ) where
  le_iff x y := by
    constructor
    · intro h
      obtain ⟨p, hp, hy⟩ :=
        (continuous_sor_instance.le_iff x.toContinuousLinearMap y.toContinuousLinearMap).mp h
      use p.toLinearMap
      exact ⟨_root_.QuantumChannel.closure_lm_of_closure_clm hp, LinearMap.toContinuousLinearMap.injective (hy.trans rfl)⟩
    · rintro ⟨p, hp, hy⟩
      apply (continuous_sor_instance.le_iff x.toContinuousLinearMap y.toContinuousLinearMap).mpr
      exact ⟨p.toContinuousLinearMap, _root_.QuantumChannel.closure_clm_of_closure_lm hp,
        congrArg LinearMap.toContinuousLinearMap hy⟩

end ContinuousLinearMapsAreCStarAlgebras


-- The structure of quantum channels
structure CPTP (ℋ₁ : Type u) (ℋ₂ : Type v) [Qudit ℋ₁] [Qudit ℋ₂]
  extends CompletelyPositiveMap (L ℋ₁) (L ℋ₂) where
  trace_map (ρ : L ℋ₁) : Tr ρ = Tr (toFun ρ)

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

-- def: Partial trace (1.121) https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
-- Tr₂(X) for X ∈ L(ℋ₁⊗ℋ₂)

noncomputable instance : Qudit (ℋ₁ ⊗[ℂ] ℋ₂) := by
  letI : Module.Finite ℂ (ℋ₁ ⊗[ℂ] ℋ₂) := inferInstance
  exact
    { toNormedAddCommGroup := inferInstance
      toInnerProductSpace := inferInstance
      toCompleteSpace := inferInstance
      fg_top := Module.Finite.fg_top }

noncomputable instance {κ : Type u} [Fintype κ] [DecidableEq κ] :
    Qudit (EuclideanSpace ℂ κ) := by
  letI : Module.Finite ℂ (EuclideanSpace ℂ κ) :=
    Module.Finite.of_basis (EuclideanSpace.basisFun κ ℂ).toBasis
  exact
    { toNormedAddCommGroup := inferInstance
      toInnerProductSpace := inferInstance
      toCompleteSpace := inferInstance
      fg_top := Module.Finite.fg_top }

noncomputable instance l_tensor_equiv {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂] :
  (L (ℋ₁ ⊗[ℂ] ℋ₂)) ≃ₗ[ℂ] (L ℋ₁ ⊗[ℂ] L ℋ₂) :=
  ((dualTensorHomEquiv ℂ (ℋ₁ ⊗[ℂ] ℋ₂) (ℋ₁ ⊗[ℂ] ℋ₂)).symm : LinearEquiv (RingHom.id ℂ) _ _).trans <|
  ((dualDistribEquiv ℂ ℋ₁ ℋ₂).symm.rTensor (ℋ₁ ⊗[ℂ] ℋ₂)).trans <|
  (TensorProduct.assoc ℂ (Module.Dual ℂ ℋ₁ ⊗[ℂ] Module.Dual ℂ ℋ₂) ℋ₁ ℋ₂).symm.trans <|
  ((TensorProduct.assoc ℂ (Module.Dual ℂ ℋ₁) (Module.Dual ℂ ℋ₂) ℋ₁).rTensor ℋ₂).trans <|
  (((TensorProduct.comm ℂ (Module.Dual ℂ ℋ₂) ℋ₁).lTensor (Module.Dual ℂ ℋ₁)).rTensor ℋ₂).trans <|
  ((TensorProduct.assoc ℂ (Module.Dual ℂ ℋ₁) ℋ₁ (Module.Dual ℂ ℋ₂)).symm.rTensor ℋ₂).trans <|
  (TensorProduct.assoc ℂ (Module.Dual ℂ ℋ₁ ⊗[ℂ] ℋ₁) (Module.Dual ℂ ℋ₂) ℋ₂).trans <|
  (TensorProduct.congr (dualTensorHomEquiv ℂ ℋ₁ ℋ₁) (dualTensorHomEquiv ℂ ℋ₂ ℋ₂))

-- It may be neccesary to add some lemmas to use l_tensor_equiv effectively

noncomputable def Tr₂ : T (ℋ₁ ⊗[ℂ] ℋ₂) ℋ₂ :=
  (TensorProduct.lid ℂ (L ℋ₂)).toLinearMap
  ∘ₗ (TensorProduct.map Tr LinearMap.id)
  ∘ₗ l_tensor_equiv.toLinearMap

lemma Tr₂_l_tensor_equiv_symm_tmul
    (X : L ℋ₁) (Y : L ℋ₂) :
    Tr₂ ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).symm (X ⊗ₜ[ℂ] Y)) = (Tr X) • Y := by
  simp [Tr₂, l_tensor_equiv]

lemma l_tensor_equiv_symm_tmul_aux
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (u : Module.Dual ℂ E ⊗[ℂ] E)
    (v : Module.Dual ℂ F ⊗[ℂ] F) :
    (l_tensor_equiv (ℋ₁ := E) (ℋ₂ := F)).symm
        ((dualTensorHom ℂ E E u) ⊗ₜ[ℂ] (dualTensorHom ℂ F F v)) =
      TensorProduct.map (dualTensorHom ℂ E E u) (dualTensorHom ℂ F F v) := by
  induction u using TensorProduct.induction_on with
  | zero =>
      simp [TensorProduct.map_zero_left]
  | tmul f p =>
      induction v using TensorProduct.induction_on with
      | zero =>
          simp [TensorProduct.map_zero_right]
      | tmul g q =>
          ext x y
          simp [l_tensor_equiv, TensorProduct.map, smul_smul]
      | add v₁ v₂ hv₁ hv₂ =>
          simp [TensorProduct.tmul_add, map_add, TensorProduct.map_add_right, hv₁, hv₂]
  | add u₁ u₂ hu₁ hu₂ =>
      simp [TensorProduct.add_tmul, map_add, TensorProduct.map_add_left, hu₁, hu₂]

lemma l_tensor_equiv_symm_tmul
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (B : L E) (C : L F) :
    (l_tensor_equiv (ℋ₁ := E) (ℋ₂ := F)).symm (B ⊗ₜ[ℂ] C) =
      TensorProduct.map B C := by
  let bE := Module.Free.chooseBasis ℂ E
  let bF := Module.Free.chooseBasis ℂ F
  let u : Module.Dual ℂ E ⊗[ℂ] E := (dualTensorHomEquivOfBasis bE).symm B
  let v : Module.Dual ℂ F ⊗[ℂ] F := (dualTensorHomEquivOfBasis bF).symm C
  have hu : dualTensorHom ℂ E E u = B := by
    simp [u]
  have hv : dualTensorHom ℂ F F v = C := by
    simp [v]
  rw [← hu, ← hv]
  exact l_tensor_equiv_symm_tmul_aux (E := E) (F := F) u v







-- def: vec(A) (1.127) https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
-- vec[|u⟩⟨v|] := |u⟩⊗|v⟩ : (ℋ₁ →L[ℂ] ℋ₂) → ℋ₂⊗ℋ₁
noncomputable def vec (b : Module.Basis ι ℂ ℋ₂) :
  (ℋ₂ →ₗ[ℂ] ℋ₁) →ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂) :=
  (TensorProduct.comm ℂ ℋ₂ ℋ₁)
  ∘ₗ (TensorProduct.map b.toDualEquiv.symm.toLinearMap LinearMap.id)
  ∘ₗ (dualTensorHomEquiv ℂ ℋ₂ ℋ₁).symm.toLinearMap

noncomputable def vecLinearEquiv (b : Module.Basis ι ℂ ℋ₂) :
    (ℋ₂ →ₗ[ℂ] ℋ₁) ≃ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂) :=
  (dualTensorHomEquiv ℂ ℋ₂ ℋ₁).symm.trans <|
    (TensorProduct.congr b.toDualEquiv.symm (LinearEquiv.refl ℂ ℋ₁)).trans <|
      TensorProduct.comm ℂ ℋ₂ ℋ₁

lemma vecLinearEquiv_toLinearMap (b : Module.Basis ι ℂ ℋ₂) :
    (vecLinearEquiv (ℋ₁ := ℋ₁) b).toLinearMap = vec b := by
  ext A
  simp [vecLinearEquiv, vec, TensorProduct.congr]

-- (1.131) (1.132) https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
-- Lemma 5.12 http://www.ueltschi.org/AZschool/notes/EricCarlen.pdf
-- For any qudit ℋ, any A,B ∈ L(ℋ), and any K ∈ L(ℋ),
-- ⟨ vec[K] ∣ (A ⊗ B) vec[K] ⟩ = Tr[K† A K B.transpose]
















lemma vec_apply (b : Module.Basis ι ℂ ℋ₂)
  (C : ℋ₂ →ₗ[ℂ] ℋ₁) :
  vec b C = ∑ i : ι, (C (b i)) ⊗ₜ[ℂ] (b i) := by
  have h : dualTensorHomEquivOfBasis b = dualTensorHomEquiv ℂ ℋ₂ ℋ₁ := by
    exact LinearEquiv.toLinearMap_inj.mp rfl
  rw [vec, ←h]
  simp only [dualTensorHomEquivOfBasis, LinearEquiv.ofLinear, Module.Basis.coe_dualBasis,
    LinearMap.coe_sum, LinearMap.coe_comp, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_symm_mk', Finset.sum_apply,
    Function.comp_apply, LinearMap.applyₗ_apply_apply, mk_apply, map_sum,
    map_tmul, LinearMap.id_coe, id_eq, comm_tmul]
  congr
  ext i
  congr
  have h : b.toDualEquiv (b i) = b.coord i := by
    simpa [Module.Basis.toDualEquiv_apply] using (Module.Basis.coe_toDual_self (b := b) i)
  rw [←h]
  exact LinearEquiv.symm_apply_apply b.toDualEquiv (b i)

lemma inner_vec_eq_trace
  (b : OrthonormalBasis ι ℂ ℋ₂)
  (A B : ℋ₂ →ₗ[ℂ] ℋ₁) :
  inner ℂ (vec b.toBasis A) (vec b.toBasis B) = Tr (A† ∘ₗ B) := by
  calc
    inner ℂ (vec b.toBasis A) (vec b.toBasis B)
        = ∑ i : ι, inner ℂ (A (b i)) (B (b i)) := by
      simp [vec_apply, inner_sum, sum_inner, b.inner_eq_ite]
    _ = ∑ i : ι, inner ℂ (b i) ((A† ∘ₗ B) (b i)) := by
      simp [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
    _ = ∑ i : ι, b.toBasis.coord i ((A† ∘ₗ B) (b i)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hcoord : b.toBasis.coord i = (innerSL ℂ (b i)).toLinearMap := by
        ext j
        simp [b.repr_apply_apply]
      simp [hcoord]
    _ = Tr (A† ∘ₗ B) := by
      simp [Tr, LinearMap.trace_eq_matrix_trace (b := b.toBasis) (f := A† ∘ₗ B),
        Matrix.trace, LinearMap.toMatrix_apply]



-- def: Choi operator (2.64) https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- J(Φ) := (Φ⊗id)(vec[I(ℋ₂⊗ℋ₁)] vec[I(ℋ₂⊗ℋ₁)]†) for Φ ∈ T(ℋ₁,ℋ₂)

-- (1.57) in https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
noncomputable def outer_product
  (u : ℋ₁) (v : ℋ₂) : ℋ₁ →ₗ[ℂ] ℋ₂ :=
  (dualTensorHomEquiv ℂ ℋ₁ ℋ₂).toLinearMap <|
    ((InnerProductSpace.toDualMap ℂ ℋ₁ u) ⊗ₜ[ℂ] v)

lemma outer_product_eq_rankOne
    (u : ℋ₁) (v : ℋ₂) :
    outer_product u v = (InnerProductSpace.rankOne ℂ v u).toLinearMap := by
  ext x
  simp [outer_product, dualTensorHom_apply]

lemma outer_product_self_nonneg
    (u : ℋ₁) :
    0 ≤ outer_product u u := by
  rw [outer_product_eq_rankOne]
  have hcont : (InnerProductSpace.rankOne ℂ u u).IsPositive :=
    InnerProductSpace.isPositive_rankOne_self (𝕜 := ℂ) u
  exact (LinearMap.nonneg_iff_isPositive _).mpr <|
    (LinearMap.isPositive_toContinuousLinearMap_iff _).mp hcont

lemma outer_product_sum
    {κ : Type*} [Fintype κ]
    (x y : κ → ℋ₁) :
    outer_product (∑ a : κ, x a) (∑ a : κ, y a) =
      ∑ a : κ, ∑ b : κ, outer_product (x a) (y b) := by
  ext z
  simp [outer_product_eq_rankOne]



noncomputable def choi (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) : L (ℋ₂ ⊗[ℂ] ℋ₁) :=
  (l_tensor_equiv.symm.toLinearMap
  ∘ₗ (TensorProduct.map Φ LinearMap.id)
  ∘ₗ l_tensor_equiv.toLinearMap) (outer_product (vec b (I ℋ₁)) (vec b (I ℋ₁)))

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

theorem isCompletelyPositive_iff_cstarMatrix_nonneg
    (Φ : T ℋ₁ ℋ₂) :
    (∃ Ψ : CompletelyPositiveMap (L ℋ₁) (L ℋ₂), Ψ.toLinearMap = Φ) ↔
      ∀ (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) (L ℋ₁)),
        0 ≤ M → 0 ≤ M.map Φ := by
  constructor
  · rintro ⟨Ψ, rfl⟩ k M hM
    exact Ψ.map_cstarMatrix_nonneg' k M hM
  · intro hΦ
    exact ⟨{ Φ with map_cstarMatrix_nonneg' := hΦ }, rfl⟩

theorem card_nonzero_eigenvalues_eq_finrank_range
    {E : Type u} [Qudit E] (T : L E) (hT : 0 ≤ T) :
    let n := Module.finrank ℂ E
    let hSym : T.IsSymmetric := (LinearMap.nonneg_iff_isPositive T).mp hT |>.isSymmetric
    Fintype.card { i : Fin n // hSym.eigenvalues rfl i ≠ 0 } =
      Module.finrank ℂ (LinearMap.range T) := by
  classical
  dsimp
  let n := Module.finrank ℂ E
  let hSym : T.IsSymmetric := (LinearMap.nonneg_iff_isPositive T).mp hT |>.isSymmetric
  have hzero :
      Fintype.card { i : Fin n // hSym.eigenvalues rfl i = 0 } =
        Module.finrank ℂ (LinearMap.ker T) := by
    have hzero' := hSym.card_filter_eigenvalues_eq (hn := rfl) (μ := (0 : ℝ))
    have hker :
        Module.finrank ℂ (Module.End.eigenspace T 0) = Module.finrank ℂ (LinearMap.ker T) := by
      simpa using congrArg (fun S : Submodule ℂ E => Module.finrank ℂ S)
        (Module.End.eigenspace_zero (R := ℂ) T)
    simpa [Fintype.card_subtype] using hzero'.trans hker
  have hcard :
      Fintype.card { i : Fin n // hSym.eigenvalues rfl i ≠ 0 } =
        n - Module.finrank ℂ (LinearMap.ker T) := by
    rw [Fintype.card_subtype_compl]
    simp [n, hzero]
  rw [hcard]
  exact by
    simp [n, (Nat.eq_sub_of_add_eq (LinearMap.finrank_range_add_finrank_ker T)).symm]

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

def IsPositiveMap (Φ : T ℋ₁ ℋ₂) : Prop :=
  ∀ X : L ℋ₁, 0 ≤ X → 0 ≤ Φ X

def IsKPositive (k : ℕ) (Φ : T ℋ₁ ℋ₂) : Prop :=
  ∀ M : CStarMatrix (Fin k) (Fin k) (L ℋ₁), 0 ≤ M → 0 ≤ M.map Φ

noncomputable def amplifyWithId (Φ : T ℋ₁ ℋ₂) : T (ℋ₁ ⊗[ℂ] ℋ₁) (ℋ₂ ⊗[ℂ] ℋ₁) :=
  l_tensor_equiv.symm.toLinearMap
    ∘ₗ (TensorProduct.map Φ LinearMap.id)
    ∘ₗ l_tensor_equiv.toLinearMap

def IsCompletelyPositive (Φ : T ℋ₁ ℋ₂) : Prop :=
  ∃ Ψ : CompletelyPositiveMap (L ℋ₁) (L ℋ₂), Ψ.toLinearMap = Φ

abbrev DS (k : ℕ) (ℋ : Type u) := PiLp 2 (fun _ : Fin k => ℋ)

noncomputable instance dsFiniteDimensional (k : ℕ) (ℋ : Type u) [Qudit ℋ] :
    FiniteDimensional ℂ (DS k ℋ) :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm.toLinearEquiv).finiteDimensional

noncomputable instance dsQudit (k : ℕ) (ℋ : Type u) [Qudit ℋ] : Qudit (DS k ℋ) where
  toNormedAddCommGroup := inferInstance
  toInnerProductSpace := inferInstance
  toCompleteSpace := inferInstance
  fg_top := by
    letI : Module.Finite ℂ (DS k ℋ) := dsFiniteDimensional k ℋ
    simpa using (Module.Finite.fg_top (R := ℂ) (M := DS k ℋ))

noncomputable def ampPlainEquiv (k : ℕ) (ℋ : Type u) [Qudit ℋ] :
    L (DS k ℋ) ≃ₐ[ℂ] Matrix (Fin k) (Fin k) (L ℋ) :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).toLinearEquiv.conjAlgEquiv ℂ).trans
    (endVecAlgEquivMatrixEnd (ι := Fin k) (R := ℂ) (A := ℂ) (M := ℋ))

lemma ampPlainEquiv_apply_apply
    (k : ℕ) (ℋ : Type u) [Qudit ℋ]
    (f : L (DS k ℋ)) (i j : Fin k) (x : ℋ) :
    ampPlainEquiv k ℋ f i j x =
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ))
        (f (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm) (Pi.single j x))) i := by
  rfl

lemma inner_symm_single
    (k : ℕ) (ℋ : Type u) [Qudit ℋ]
    (v : DS k ℋ) (i : Fin k) (x : ℋ) :
    inner ℂ v (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm) (Pi.single i x)) =
      inner ℂ (v i) x := by
  rw [PiLp.inner_apply]
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro hi
    simp at hi

lemma inner_single_symm
    (k : ℕ) (ℋ : Type u) [Qudit ℋ]
    (i : Fin k) (x : ℋ) (v : DS k ℋ) :
    inner ℂ (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm) (Pi.single i x)) v =
      inner ℂ x (v i) := by
  rw [PiLp.inner_apply]
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro hi
    simp at hi

lemma inner_coord_right
    (k : ℕ) (ℋ : Type u) [Qudit ℋ]
    (z : DS k ℋ) (i : Fin k) (y : ℋ) :
    inner ℂ ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)) z i) y =
      inner ℂ z (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm) (Pi.single i y)) := by
  simpa using (inner_symm_single (k := k) (ℋ := ℋ) (v := z) (i := i) (x := y)).symm

lemma inner_coord_left
    (k : ℕ) (ℋ : Type u) [Qudit ℋ]
    (i : Fin k) (x : ℋ) (z : DS k ℋ) :
    inner ℂ x ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)) z i) =
      inner ℂ (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm) (Pi.single i x)) z := by
  simpa using (inner_single_symm (k := k) (ℋ := ℋ) (i := i) (x := x) (v := z)).symm

lemma ampPlainEquiv_map_star
    (k : ℕ) (ℋ : Type u) [Qudit ℋ]
    (f : L (DS k ℋ)) :
    ampPlainEquiv k ℋ (star f) = star (ampPlainEquiv k ℋ f) := by
  ext i j x
  apply ext_inner_right ℂ
  intro y
  rw [ampPlainEquiv_apply_apply, Matrix.star_apply]
  have hstar :
      inner ℂ ((star ((ampPlainEquiv k ℋ) f j i)) x) y =
        inner ℂ x ((ampPlainEquiv k ℋ f j i) y) := by
    change inner ℂ (((ampPlainEquiv k ℋ f j i)†) x) y =
      inner ℂ x ((ampPlainEquiv k ℋ f j i) y)
    simpa using
      (LinearMap.adjoint_inner_left (A := ampPlainEquiv k ℋ f j i) (x := y) (y := x))
  rw [hstar, ampPlainEquiv_apply_apply, inner_coord_right, inner_coord_left]
  simpa using
    (LinearMap.adjoint_inner_left
      (A := f)
      (x := ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm (Pi.single i y)))
      (y := ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm (Pi.single j x))))

noncomputable def ampMatrixStarAlgEquiv (k : ℕ) (ℋ : Type u) [Qudit ℋ] :
    L (DS k ℋ) ≃⋆ₐ[ℂ] Matrix (Fin k) (Fin k) (L ℋ) :=
  StarAlgEquiv.ofAlgEquiv (ampPlainEquiv k ℋ) (ampPlainEquiv_map_star (k := k) (ℋ := ℋ))

noncomputable def ampCStarEquiv (k : ℕ) (ℋ : Type u) [Qudit ℋ] :
    L (DS k ℋ) ≃⋆ₐ[ℂ] CStarMatrix (Fin k) (Fin k) (L ℋ) :=
  (ampMatrixStarAlgEquiv k ℋ).trans CStarMatrix.ofMatrixStarAlgEquiv

noncomputable def ampSuper
    (k : ℕ) (Φ : T ℋ₁ ℋ₂) : T (DS k ℋ₁) (DS k ℋ₂) :=
  (ampCStarEquiv k ℋ₂).symm.toAlgEquiv.toLinearMap ∘ₗ
    (CStarMatrix.mapₗ Φ) ∘ₗ
      (ampCStarEquiv k ℋ₁).toAlgEquiv.toLinearMap

lemma ampCStarEquiv_ampSuper_apply
    (k : ℕ) (Φ : T ℋ₁ ℋ₂) (A : L (DS k ℋ₁)) :
    ampCStarEquiv k ℋ₂ (ampSuper k Φ A) = (ampCStarEquiv k ℋ₁ A).map Φ := by
  change
    ampCStarEquiv k ℋ₂
      ((ampCStarEquiv k ℋ₂).symm (((ampCStarEquiv k ℋ₁) A).map Φ)) =
        ((ampCStarEquiv k ℋ₁) A).map Φ
  exact (ampCStarEquiv k ℋ₂).apply_symm_apply _

lemma starAlgEquiv_mem_nonnegClosure
    {A B : Type*}
    [Semiring A] [StarRing A] [Algebra ℂ A] [PartialOrder A] [StarOrderedRing A]
    [Semiring B] [StarRing B] [Algebra ℂ B] [PartialOrder B] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B) {x : A}
    (hx : x ∈ AddSubmonoid.closure (Set.range fun s : A => star s * s)) :
    e x ∈ AddSubmonoid.closure (Set.range fun t : B => star t * t) := by
  induction hx using AddSubmonoid.closure_induction with
  | mem y hy =>
      obtain ⟨s, rfl⟩ := hy
      refine AddSubmonoid.subset_closure ⟨e s, ?_⟩
      simpa using congrArg (fun z => z * e s) (map_star e s).symm
  | zero =>
      rw [map_zero]
      exact AddSubmonoid.zero_mem (AddSubmonoid.closure (Set.range fun t : B => star t * t))
  | add y z _ _ ihy ihz =>
      rw [map_add]
      exact AddSubmonoid.add_mem (AddSubmonoid.closure (Set.range fun t : B => star t * t)) ihy ihz

lemma starAlgEquiv_nonneg
    {A B : Type*}
    [Semiring A] [StarRing A] [Algebra ℂ A] [PartialOrder A] [StarOrderedRing A]
    [Semiring B] [StarRing B] [Algebra ℂ B] [PartialOrder B] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B) {x : A} (hx : 0 ≤ x) :
    0 ≤ e x := by
  refine StarOrderedRing.nonneg_iff.mpr ?_
  exact starAlgEquiv_mem_nonnegClosure e (StarOrderedRing.nonneg_iff.mp hx)

lemma starAlgEquiv_nonneg_iff
    {A B : Type*}
    [Semiring A] [StarRing A] [Algebra ℂ A] [PartialOrder A] [StarOrderedRing A]
    [Semiring B] [StarRing B] [Algebra ℂ B] [PartialOrder B] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B) {x : A} :
    0 ≤ e x ↔ 0 ≤ x := by
  constructor
  · intro hx
    simpa using starAlgEquiv_nonneg e.symm hx
  · intro hx
    exact starAlgEquiv_nonneg e hx

lemma isKPositive_iff_isPositiveMap_ampSuper
    (k : ℕ) (Φ : T ℋ₁ ℋ₂) :
    IsKPositive k Φ ↔ IsPositiveMap (ampSuper k Φ) := by
  constructor
  · intro hΦ A hA
    have hAmap :
        0 ≤ ampCStarEquiv k ℋ₁ A := starAlgEquiv_nonneg (ampCStarEquiv k ℋ₁) hA
    have hMap :
        0 ≤ ampCStarEquiv k ℋ₂ (ampSuper k Φ A) := by
      rw [ampCStarEquiv_ampSuper_apply]
      exact hΦ _ hAmap
    exact (starAlgEquiv_nonneg_iff (ampCStarEquiv k ℋ₂)).1 hMap
  · intro hΦ M hM
    let A : L (DS k ℋ₁) := (ampCStarEquiv k ℋ₁).symm M
    have hMA : ampCStarEquiv k ℋ₁ A = M := by
      simp [A]
    have hA : 0 ≤ A := by
      have hM' : 0 ≤ ampCStarEquiv k ℋ₁ A := by simpa [hMA] using hM
      exact (starAlgEquiv_nonneg_iff (ampCStarEquiv k ℋ₁)).1 hM'
    have hAmp : 0 ≤ ampSuper k Φ A := hΦ A hA
    have hMap : 0 ≤ ampCStarEquiv k ℋ₂ (ampSuper k Φ A) :=
      starAlgEquiv_nonneg (ampCStarEquiv k ℋ₂) hAmp
    have hEq :
        ampCStarEquiv k ℋ₂ (ampSuper k Φ A) = (ampCStarEquiv k ℋ₁ A).map Φ :=
      ampCStarEquiv_ampSuper_apply (k := k) (Φ := Φ) (A := A)
    simpa [hEq, hMA] using hMap

theorem completelyPositive_to_positiveMap
    (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ → IsPositiveMap Φ := by
  rintro ⟨Ψ, rfl⟩ X hX
  exact map_nonneg Ψ hX



lemma comp_outer_product_adjoint
    {ℋ₃ : Type w} [Qudit ℋ₃]
    (A : ℋ₁ →ₗ[ℂ] ℋ₃) (u v : ℋ₁) :
    A.comp ((outer_product u v).comp (LinearMap.adjoint A)) =
      outer_product (A u) (A v) := by
  ext y
  simp [outer_product_eq_rankOne, LinearMap.adjoint_inner_right]

noncomputable def krausTerm
    (V : ℋ₁ →ₗ[ℂ] ℋ₂) : T ℋ₁ ℋ₂ where
  toFun := fun A => V ∘ₗ A ∘ₗ V†
  map_add' := by
    intro A B
    ext x
    simp [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' := by
    intro c A
    ext x
    simp [LinearMap.smul_comp, LinearMap.comp_smul]

lemma krausTerm_isPositiveMap
    (V : ℋ₁ →ₗ[ℂ] ℋ₂) :
    IsPositiveMap (krausTerm V) := by
  intro A hA
  have hAclm : A.toContinuousLinearMap.IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).1 (by simpa using hA)
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).2 <| by
    simpa [krausTerm, LinearMap.comp_assoc, LinearMap.star_eq_adjoint,
      ContinuousLinearMap.coe_comp] using hAclm.conj_adjoint V.toContinuousLinearMap

noncomputable def dsEquiv (k : ℕ) (ℋ : Type*) [Qudit ℋ] :
    DS k ℋ ≃L[ℂ] (Fin k → ℋ) :=
  PiLp.continuousLinearEquiv (p := (2 : ENNReal)) (𝕜 := ℂ) (β := fun _ : Fin k => ℋ)

noncomputable def dsProj (k : ℕ) (ℋ : Type*) [Qudit ℋ] (i : Fin k) :
    DS k ℋ →L[ℂ] ℋ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℋ) i) ∘L
    (dsEquiv k ℋ).toContinuousLinearMap

noncomputable def dsIncl (k : ℕ) (ℋ : Type*) [Qudit ℋ] (i : Fin k) :
    ℋ →L[ℂ] DS k ℋ :=
  (dsEquiv k ℋ).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.single ℂ (fun _ : Fin k => ℋ) i)

lemma dsProj_dsIncl_apply
    (k : ℕ) (ℋ : Type*) [Qudit ℋ] (i j : Fin k) (x : ℋ) :
    dsProj k ℋ i (dsIncl k ℋ j x) = if i = j then x else 0 := by
  by_cases h : i = j
  · subst h
    simp [dsProj, dsIncl, dsEquiv]
  · simp [dsProj, dsIncl, dsEquiv, h]

lemma dsIncl_adjoint
    (k : ℕ) (ℋ : Type*) [Qudit ℋ] (i : Fin k) :
    (dsIncl k ℋ i).adjoint = dsProj k ℋ i := by
  apply ContinuousLinearMap.ext
  intro x
  refine ext_inner_right ℂ fun y => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  simpa [dsProj, dsIncl, dsEquiv] using
    (inner_symm_single (k := k) (ℋ := ℋ) (v := x) (i := i) (x := y))



noncomputable def ampKrausFactorCLM
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) : DS k ℋ₁ →L[ℂ] DS k ℋ₂ :=
  ∑ i : Fin k, ((dsIncl k ℋ₂ i).comp V.toContinuousLinearMap).comp (dsProj k ℋ₁ i)

noncomputable def ampKrausFactor
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) : DS k ℋ₁ →ₗ[ℂ] DS k ℋ₂ :=
  (ampKrausFactorCLM k V).toLinearMap

lemma dsProj_ampKrausFactorCLM
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) (i : Fin k) (x : DS k ℋ₁) :
    dsProj k ℋ₂ i (ampKrausFactorCLM k V x) = V (dsProj k ℋ₁ i x) := by
  classical
  simp [ampKrausFactorCLM, Finset.sum_apply, dsProj_dsIncl_apply]

lemma ampKrausFactorCLM_dsIncl
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) (i : Fin k) (x : ℋ₁) :
    ampKrausFactorCLM k V (dsIncl k ℋ₁ i x) = dsIncl k ℋ₂ i (V x) := by
  apply (dsEquiv k ℋ₂).injective
  ext j
  have h :=
    dsProj_ampKrausFactorCLM (k := k) (V := V) (i := j) (x := dsIncl k ℋ₁ i x)
  by_cases hji : j = i
  · subst hji
    simpa [dsProj, dsIncl, dsEquiv] using h
  · simpa [dsProj, dsIncl, dsEquiv, hji] using h

lemma ampKrausFactorCLM_adjoint_dsIncl
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) (i : Fin k) (x : ℋ₂) :
    (ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x) = dsIncl k ℋ₁ i (V.adjoint x) := by
  classical
  apply (dsEquiv k ℋ₁).injective
  ext j
  apply ext_inner_right ℂ
  intro y
  rw [show
      inner ℂ
          ((dsEquiv k ℋ₁) ((ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x)) j) y =
        inner ℂ
          (dsProj k ℋ₁ j ((ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x))) y by
      rfl]
  rw [show
      inner ℂ ((dsEquiv k ℋ₁) (dsIncl k ℋ₁ i (V.adjoint x)) j) y =
        inner ℂ (dsProj k ℋ₁ j (dsIncl k ℋ₁ i (V.adjoint x))) y by
      rfl]
  by_cases hji : j = i
  · subst j
    calc
      inner ℂ
          (dsProj k ℋ₁ i ((ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x))) y =
        inner ℂ ((ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x))
          (dsIncl k ℋ₁ i y) := by
          simpa [dsIncl_adjoint] using
            (ContinuousLinearMap.adjoint_inner_left
              (A := dsIncl k ℋ₁ i)
              (x := y)
              (y := (ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x)))
      _ = inner ℂ (dsIncl k ℋ₂ i x)
          (ampKrausFactorCLM k V (dsIncl k ℋ₁ i y)) := by
          exact ContinuousLinearMap.adjoint_inner_left
            (A := ampKrausFactorCLM k V)
            (x := dsIncl k ℋ₁ i y)
            (y := dsIncl k ℋ₂ i x)
      _ = inner ℂ (dsIncl k ℋ₂ i x) (dsIncl k ℋ₂ i (V y)) := by
          rw [ampKrausFactorCLM_dsIncl]
      _ = inner ℂ (V.adjoint x) y := by
          rw [← ContinuousLinearMap.adjoint_inner_right
            (A := dsIncl k ℋ₂ i)
            (x := x)
            (y := dsIncl k ℋ₂ i (V y))]
          simp [dsIncl_adjoint, dsProj_dsIncl_apply,
            LinearMap.adjoint_inner_left]
      _ = inner ℂ (dsProj k ℋ₁ i (dsIncl k ℋ₁ i (V.adjoint x))) y := by
          simp [dsProj_dsIncl_apply]
  · calc
      inner ℂ
          (dsProj k ℋ₁ j ((ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x))) y =
        inner ℂ ((ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x))
          (dsIncl k ℋ₁ j y) := by
          simpa [dsIncl_adjoint] using
            (ContinuousLinearMap.adjoint_inner_left
              (A := dsIncl k ℋ₁ j)
              (x := y)
              (y := (ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x)))
      _ = inner ℂ (dsIncl k ℋ₂ i x)
          (ampKrausFactorCLM k V (dsIncl k ℋ₁ j y)) := by
          exact ContinuousLinearMap.adjoint_inner_left
            (A := ampKrausFactorCLM k V)
            (x := dsIncl k ℋ₁ j y)
            (y := dsIncl k ℋ₂ i x)
      _ = inner ℂ (dsIncl k ℋ₂ i x) (dsIncl k ℋ₂ j (V y)) := by
          rw [ampKrausFactorCLM_dsIncl]
      _ = 0 := by
          rw [← ContinuousLinearMap.adjoint_inner_right
            (A := dsIncl k ℋ₂ i)
            (x := x)
            (y := dsIncl k ℋ₂ j (V y))]
          have hij : i ≠ j := fun hij => hji hij.symm
          simp [dsIncl_adjoint, dsProj_dsIncl_apply, hij]
      _ = inner ℂ (dsProj k ℋ₁ j (dsIncl k ℋ₁ i (V.adjoint x))) y := by
          simp [dsProj_dsIncl_apply, hji]

lemma ampKrausFactor_adjoint_dsIncl
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) (i : Fin k) (x : ℋ₂) :
    ((ampKrausFactor k V)†) (dsIncl k ℋ₂ i x) = dsIncl k ℋ₁ i (V.adjoint x) := by
  change (ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x) = dsIncl k ℋ₁ i (V.adjoint x)
  exact ampKrausFactorCLM_adjoint_dsIncl (k := k) (V := V) (i := i) (x := x)

lemma dsProj_ampKrausFactor
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) (i : Fin k) (x : DS k ℋ₁) :
    dsProj k ℋ₂ i (ampKrausFactor k V x) = V (dsProj k ℋ₁ i x) := by
  exact dsProj_ampKrausFactorCLM (k := k) (V := V) (i := i) (x := x)



lemma ampPlainEquiv_apply_apply_ds
    (k : ℕ) (ℋ : Type*) [Qudit ℋ]
    (f : L (DS k ℋ)) (i j : Fin k) (x : ℋ) :
    ampPlainEquiv k ℋ f i j x = dsProj k ℋ i (f (dsIncl k ℋ j x)) := by
  simpa [dsProj, dsIncl, dsEquiv] using
    (ampPlainEquiv_apply_apply (k := k) (ℋ := ℋ) (f := f) (i := i) (j := j) (x := x))
end RepresentationsOfChannels
end QuantumChannel


