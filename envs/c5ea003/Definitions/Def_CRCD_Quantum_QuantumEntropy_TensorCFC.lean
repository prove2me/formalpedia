-- Prove2me | Definitions.Def_CRCD_Quantum_QuantumEntropy_TensorCFC
-- name    : CRCD_Quantum_QuantumEntropy_TensorCFC
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T23:55:34.899741+00:00
-- url     : https://prove2.me/theorems/1b68d638-c996-4a77-9e7d-1836d4158d60
-- title:
--   Tensor-factor star-algebra homomorphisms
-- statement:
--   Let $H,K$ be finite-dimensional complex Hilbert spaces. Acting on one tensor factor defines complex star-algebra homomorphisms
--
--   $$\iota_H:\operatorname{End}(H)\to\operatorname{End}(H\otimes K),\quad\iota_H(A)=A\otimes I_K,\qquad\iota_K:\operatorname{End}(K)\to\operatorname{End}(H\otimes K),\quad\iota_K(B)=I_H\otimes B.$$
--
--   They preserve identity, addition, complex scalars, composition, and adjoints. Thus their actions on elementary tensors are $(A\otimes I_K)(x\otimes y)=Ax\otimes y$ and $(I_H\otimes B)(x\otimes y)=x\otimes By$. Nonnegative-real/complex scalar-tower instances are provided on both factor algebras and the tensor-product algebra. These interfaces transport continuous functional calculus through tensor-factor embeddings in the tensor-power and entropy multiplicativity arguments.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumEntropy/TensorCFC.lean#L51-L521

import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumChannel_part_4
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumState

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/













/-!
# Tensor product CFC infrastructure

Infrastructure for the continuous functional calculus on tensor products,
proving that `CFC.rpow` distributes over tensor products of operators:
`(A ⊗ B)^p = A^p ⊗ B^p`.

## Strategy

Factor `TensorProduct.map A B = A.rTensor ℋ₂ * B.lTensor ℋ₁` where the two factors commute,
then use `StarAlgHomClass.map_cfc` to distribute `CFC.rpow` through each factor.

## Main results

* `TensorCFC.rTensorStarAlgHom` / `lTensorStarAlgHom`:
  The maps `A ↦ A.rTensor ℋ₂` and `B ↦ B.lTensor ℋ₁` as star algebra homomorphisms.
* `TensorCFC.rpow_rTensor` / `rpow_lTensor`:
  `CFC.rpow` distributes through `rTensor` / `lTensor`.
* `TensorCFC.rpow_tensorProduct`:
  `CFC.rpow (map A B) p = map (CFC.rpow A p) (CFC.rpow B p)` (modulo `rpow_mul_comm_nonneg`).
-/

open QuantumState QuantumChannel TensorProduct
open scoped NNReal Polynomial

namespace TensorCFC

universe u v
variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
variable [Nontrivial ℋ₁] [Nontrivial ℋ₂]

/-! ### Scalar tower instances -/

instance instIsScalarTower₁ : IsScalarTower ℝ≥0 ℂ (L ℋ₁) :=
  ⟨fun r s a => smul_assoc (r : ℂ) s a⟩
instance instIsScalarTower₂ : IsScalarTower ℝ≥0 ℂ (L ℋ₂) :=
  ⟨fun r s a => smul_assoc (r : ℂ) s a⟩
instance instIsScalarTowerTensor : IsScalarTower ℝ≥0 ℂ (L (ℋ₁ ⊗[ℂ] ℋ₂)) :=
  ⟨fun r s a => smul_assoc (r : ℂ) s a⟩

/-! ### Star algebra homomorphisms for rTensor / lTensor -/

noncomputable def rTensorStarAlgHom : L ℋ₁ →⋆ₐ[ℂ] L (ℋ₁ ⊗[ℂ] ℋ₂) where
  toFun f := f.rTensor ℋ₂
  map_one' := TensorProduct.ext' fun _ _ => rfl
  map_mul' _ _ := TensorProduct.ext' fun _ _ => by simp
  map_zero' := TensorProduct.ext' fun _ _ => by simp
  map_add' _ _ := TensorProduct.ext' fun _ _ => by simp
  commutes' r := TensorProduct.ext' fun _ _ => by
    simp [Algebra.algebraMap_eq_smul_one, smul_tmul']
  map_star' f := by
    simp only [LinearMap.star_eq_adjoint]
    exact (LinearMap.adjoint_rTensor f).symm

noncomputable def lTensorStarAlgHom : L ℋ₂ →⋆ₐ[ℂ] L (ℋ₁ ⊗[ℂ] ℋ₂) where
  toFun g := g.lTensor ℋ₁
  map_one' := TensorProduct.ext' fun _ _ => rfl
  map_mul' _ _ := TensorProduct.ext' fun _ _ => by simp
  map_zero' := TensorProduct.ext' fun _ _ => by simp
  map_add' _ _ := TensorProduct.ext' fun _ _ => by simp
  commutes' r := TensorProduct.ext' fun _ _ => by
    simp [Algebra.algebraMap_eq_smul_one, smul_tmul']
  map_star' g := by
    simp only [LinearMap.star_eq_adjoint]
    exact (LinearMap.adjoint_lTensor g).symm

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
@[simp] lemma rTensorStarAlgHom_apply (f : L ℋ₁) :
    (rTensorStarAlgHom (ℋ₂ := ℋ₂)) f = f.rTensor ℋ₂ := rfl

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
@[simp] lemma lTensorStarAlgHom_apply (g : L ℋ₂) :
    (lTensorStarAlgHom (ℋ₁ := ℋ₁)) g = g.lTensor ℋ₁ := rfl

/-! ### Factorization and commutativity -/

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma map_eq_rTensor_mul_lTensor (f : L ℋ₁) (g : L ℋ₂) :
    (TensorProduct.map f g : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
      (rTensorStarAlgHom (ℋ₂ := ℋ₂)) f * (lTensorStarAlgHom (ℋ₁ := ℋ₁)) g :=
  TensorProduct.ext' fun x y => by
    simp only [rTensorStarAlgHom_apply, lTensorStarAlgHom_apply]
    change TensorProduct.map f g (x ⊗ₜ y) =
      (f.rTensor ℋ₂).comp (g.lTensor ℋ₁) (x ⊗ₜ y)
    simp





/-! ### Continuity -/



omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma continuous_lTensorStarAlgHom :
    Continuous (lTensorStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)) :=
  (lTensorStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).toAlgHom.toLinearMap.continuous_of_finiteDimensional

/-! ### Nonneg preservation -/





/-! ### Unit reflection for rTensor / lTensor

In finite dimensions, `B.rTensor ℋ₂` is a unit iff `B` is a unit.
The forward direction uses a basis element to embed `ker B` into `ker (B.rTensor ℋ₂)`.
The reverse follows from flatness. -/













/-! ### Spectrum equality for tensor embeddings -/













/-! ### CFC distribution through rTensor / lTensor -/





/-! ### CFC eigenvalue property

In finite dimensions, the CFC maps eigenvectors to eigenvectors with eigenvalues
transformed by the function: if `T v = μ • v` then `cfc f T v = f(μ) • v`.
The proof uses Lagrange interpolation on the finite spectrum combined with
`cfc_congr` and `cfc_polynomial`. -/

 lemma isScalarTower_real {ℋ : Type*} [Qudit ℋ] :
    IsScalarTower ℝ ℂ (L ℋ) :=
  ⟨fun r s a => by
    change ((r : ℂ) • s) • a = (r : ℂ) • s • a
    rw [smul_assoc]⟩

 lemma pow_apply_eigenvector {ℋ : Type*} [Qudit ℋ]
    (T : L ℋ) (μ : ℂ) (v : ℋ) (hv : T v = μ • v) (n : ℕ) :
    (T ^ n) v = μ ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : (T ^ (n + 1)) v = (T ^ n) (T v) := rfl
    rw [this, hv, map_smul, ih, smul_smul, pow_succ']

 lemma aeval_apply_eigenvector {ℋ : Type*} [Qudit ℋ]
    (T : L ℋ) (μ : ℂ) (v : ℋ) (hv : T v = μ • v) (q : ℝ[X]) :
    (Polynomial.aeval T q) v = (Polynomial.aeval μ q) • v := by
  haveI := _root_.TensorCFC.isScalarTower_real (ℋ := ℋ)
  induction q using Polynomial.induction_on' with
  | add p₁ p₂ hp₁ hp₂ =>
    simp only [map_add, LinearMap.add_apply, hp₁, hp₂, add_smul]
  | monomial n r =>
    simp only [Polynomial.aeval_monomial]
    change (algebraMap ℝ (L ℋ) r) ((T ^ n) v) = _
    rw [_root_.TensorCFC.pow_apply_eigenvector T μ v hv n, map_smul,
        IsScalarTower.algebraMap_apply ℝ ℂ (L ℋ)]
    simp only [Module.algebraMap_end_apply, smul_smul, mul_comm]

 lemma spectrum_real_finite {ℋ : Type*} [Qudit ℋ]
    (T : L ℋ) : Set.Finite (spectrum ℝ T) := by
  haveI := _root_.TensorCFC.isScalarTower_real (ℋ := ℋ)
  rw [← spectrum.preimage_algebraMap ℂ (R := ℝ)]
  exact (Module.End.finite_spectrum T).preimage
    (fun _ _ _ _ h => RCLike.ofReal_injective h)

 lemma cfc_apply_eigenvector {ℋ : Type*} [Qudit ℋ]
    (T : L ℋ) (hT_sa : IsSelfAdjoint T) (f : ℝ → ℝ)
    (v : ℋ) (μ : ℝ) (hv : T v = (algebraMap ℝ ℂ μ) • v) (hμ : μ ∈ spectrum ℝ T) :
    (cfc f T : L ℋ) v = (algebraMap ℝ ℂ (f μ)) • v := by
  haveI := _root_.TensorCFC.isScalarTower_real (ℋ := ℋ)
  have hfin := _root_.TensorCFC.spectrum_real_finite T
  set S := hfin.toFinset
  have hS_mem : ∀ x : ℝ, x ∈ S ↔ x ∈ spectrum ℝ T := fun x => hfin.mem_toFinset
  have hμ_mem_S : μ ∈ S := (hS_mem μ).mpr hμ
  have hinj : Set.InjOn (id : ℝ → ℝ) (↑S : Set ℝ) :=
    Function.injective_id.injOn
  let q := Lagrange.interpolate S id (fun s => f s)
  have hq_eval : ∀ x ∈ S, Polynomial.eval x q = f x :=
    fun x hx => Lagrange.eval_interpolate_at_node (fun s => f s) hinj hx
  have hcfc_eq : cfc f T = cfc q.eval T := by
    apply cfc_congr
    intro x hx
    exact (hq_eval x ((hS_mem x).mpr hx)).symm
  have hpoly : cfc q.eval T = Polynomial.aeval T q :=
    cfc_polynomial q T
  rw [hcfc_eq, hpoly, _root_.TensorCFC.aeval_apply_eigenvector T (algebraMap ℝ ℂ μ) v hv q]
  congr 1
  rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
  congr 1
  exact hq_eval μ hμ_mem_S

/-! ### Main result: rpow distributes over tensor products

Proved directly using eigenvector bases for A and B. The tensor product
of eigenvector bases provides a basis for `ℋ₁ ⊗ ℋ₂` of simultaneous
eigenvectors, reducing the proof to the scalar identity `(λμ)^p = λ^p μ^p`. -/

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
 lemma star_map (A : L ℋ₁) (B : L ℋ₂) :
    star (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
      TensorProduct.map (star A) (star B) := by
  simp only [LinearMap.star_eq_adjoint, TensorProduct.adjoint_map]

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
 lemma isSelfAdjoint_map_of_nonneg (A : L ℋ₁) (B : L ℋ₂)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    IsSelfAdjoint (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) := by
  rw [IsSelfAdjoint, _root_.TensorCFC.star_map, (IsSelfAdjoint.of_nonneg hA).star_eq,
      (IsSelfAdjoint.of_nonneg hB).star_eq]

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
 lemma map_nonneg_of_nonneg (A : L ℋ₁) (B : L ℋ₂)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) := by
  set sA := CFC.sqrt A
  set sB := CFC.sqrt B
  have hsA := CFC.sqrt_nonneg A
  have hsB := CFC.sqrt_nonneg B
  have : TensorProduct.map A B =
      star (TensorProduct.map sA sB) * TensorProduct.map sA sB := by
    rw [_root_.TensorCFC.star_map, (IsSelfAdjoint.of_nonneg hsA).star_eq,
        (IsSelfAdjoint.of_nonneg hsB).star_eq, ← TensorProduct.map_mul,
        CFC.sqrt_mul_sqrt_self A, CFC.sqrt_mul_sqrt_self B]
  rw [this]
  exact star_mul_self_nonneg _

 lemma eigenvalue_nonneg_of_nonneg {ℋ : Type*} [Qudit ℋ]
    {n : ℕ} (T : L ℋ) (hT : 0 ≤ T) (hT_sym : T.IsSymmetric) (hn : Module.finrank ℂ ℋ = n)
    (i : Fin n) : 0 ≤ hT_sym.eigenvalues hn i := by
  have hpos := (LinearMap.nonneg_iff_isPositive T).mp hT
  set v := hT_sym.eigenvectorBasis hn i
  have hv_ne : v ≠ 0 := (hT_sym.eigenvectorBasis hn).toBasis.ne_zero i
  have hinn := hpos.2 v
  rw [hT_sym.apply_eigenvectorBasis, inner_smul_left, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul] at hinn
  refine nonneg_of_mul_nonneg_left hinn ?_
  rw [inner_self_eq_norm_sq]
  exact pow_pos (norm_pos_iff.mpr hv_ne) 2

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
set_option backward.isDefEq.respectTransparency false in
theorem rpow_tensorProduct (A : L ℋ₁) (B : L ℋ₂) (p : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    CFC.rpow (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) p =
      TensorProduct.map (CFC.rpow A p) (CFC.rpow B p) := by
  haveI := _root_.TensorCFC.isScalarTower_real (ℋ := ℋ₁ ⊗[ℂ] ℋ₂)
  have hA_sa := IsSelfAdjoint.of_nonneg hA
  have hB_sa := IsSelfAdjoint.of_nonneg hB
  have hA_sym := (LinearMap.isSymmetric_iff_isSelfAdjoint A).mpr hA_sa
  have hB_sym := (LinearMap.isSymmetric_iff_isSelfAdjoint B).mpr hB_sa
  have hAB_sa := _root_.TensorCFC.isSelfAdjoint_map_of_nonneg A B hA hB
  set n₁ := Module.finrank ℂ ℋ₁
  set n₂ := Module.finrank ℂ ℋ₂
  set eA := hA_sym.eigenvectorBasis (rfl : Module.finrank ℂ ℋ₁ = n₁)
  set eB := hB_sym.eigenvectorBasis (rfl : Module.finrank ℂ ℋ₂ = n₂)
  set eigA := hA_sym.eigenvalues (rfl : Module.finrank ℂ ℋ₁ = n₁)
  set eigB := hB_sym.eigenvalues (rfl : Module.finrank ℂ ℋ₂ = n₂)
  set f : ℝ → ℝ := fun x => ((x.toNNReal) ^ p : ℝ≥0)
  have hA_eig : ∀ i, A (eA i) = (algebraMap ℝ ℂ (eigA i)) • (eA i) := by
    intro i; rw [RCLike.algebraMap_eq_ofReal]; exact hA_sym.apply_eigenvectorBasis _ i
  have hB_eig : ∀ j, B (eB j) = (algebraMap ℝ ℂ (eigB j)) • (eB j) := by
    intro j; rw [RCLike.algebraMap_eq_ofReal]; exact hB_sym.apply_eigenvectorBasis _ j
  have heigA_nonneg : ∀ i, 0 ≤ eigA i :=
    fun i => _root_.TensorCFC.eigenvalue_nonneg_of_nonneg A hA hA_sym _ i
  have heigB_nonneg : ∀ j, 0 ≤ eigB j :=
    fun j => _root_.TensorCFC.eigenvalue_nonneg_of_nonneg B hB hB_sym _ j
  have hAB_nn := _root_.TensorCFC.map_nonneg_of_nonneg A B hA hB
  -- Convert CFC.rpow to real-valued cfc via cfc_nnreal_eq_real
  have hrpow_eq_A : CFC.rpow A p = cfc f A := cfc_nnreal_eq_real ..
  have hrpow_eq_B : CFC.rpow B p = cfc f B := cfc_nnreal_eq_real ..
  have hrpow_eq_AB : CFC.rpow (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) p =
      cfc f (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) := cfc_nnreal_eq_real ..
  rw [hrpow_eq_A, hrpow_eq_B, hrpow_eq_AB]
  -- Prove by extension on the tensor product eigenvector basis
  apply (eA.toBasis.tensorProduct eB.toBasis).ext
  intro ⟨i, j⟩
  have htb : (eA.toBasis.tensorProduct eB.toBasis) (i, j) = eA i ⊗ₜ eB j := by
    rw [eA.toBasis.tensorProduct_apply]; simp [OrthonormalBasis.coe_toBasis]
  rw [htb, map_tmul]
  -- RHS: (cfc f A) (eA i) ⊗ₜ (cfc f B) (eB j)
  have heigA_spec : ∀ i, eigA i ∈ spectrum ℝ A := by
    intro i
    rw [← spectrum.preimage_algebraMap ℂ (R := ℝ), Set.mem_preimage]
    exact (hA_sym.hasEigenvalue_eigenvalues _ i).mem_spectrum
  have heigB_spec : ∀ j, eigB j ∈ spectrum ℝ B := by
    intro j
    rw [← spectrum.preimage_algebraMap ℂ (R := ℝ), Set.mem_preimage]
    exact (hB_sym.hasEigenvalue_eigenvalues _ j).mem_spectrum
  rw [_root_.TensorCFC.cfc_apply_eigenvector A hA_sa f (eA i) (eigA i) (hA_eig i) (heigA_spec i),
      _root_.TensorCFC.cfc_apply_eigenvector B hB_sa f (eB j) (eigB j) (hB_eig j) (heigB_spec j)]
  have hAB_eig : (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) (eA i ⊗ₜ eB j) =
      (algebraMap ℝ ℂ (eigA i * eigB j)) • (eA i ⊗ₜ eB j) := by
    rw [map_tmul, hA_eig i, hB_eig j, TensorProduct.smul_tmul_smul, ← map_mul]
  have hAB_spec : eigA i * eigB j ∈ spectrum ℝ (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) := by
    rw [← spectrum.preimage_algebraMap ℂ (R := ℝ), Set.mem_preimage]
    rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
    rw [Module.End.hasEigenvalue_iff]
    intro heq
    have hmem : eA i ⊗ₜ[ℂ] eB j ∈ (⊥ : Submodule ℂ (ℋ₁ ⊗[ℂ] ℋ₂)) :=
      heq ▸ Module.End.mem_eigenspace_iff.mpr hAB_eig
    rw [Submodule.mem_bot] at hmem
    have htp := eA.toBasis.tensorProduct_apply eB.toBasis i j
    exact (eA.toBasis.tensorProduct eB.toBasis).ne_zero (i, j) (htp.trans hmem)
  rw [_root_.TensorCFC.cfc_apply_eigenvector _ hAB_sa f _ _ hAB_eig hAB_spec]
  -- Now both sides have form scalar • (eA i ⊗ₜ eB j), show scalars agree
  -- LHS: algebraMap ℝ ℂ (f (eigA i * eigB j)) • (eA i ⊗ₜ eB j)
  -- RHS: (algebraMap ℝ ℂ (f (eigA i))) • eA i ⊗ₜ (algebraMap ℝ ℂ (f (eigB j))) • eB j
  -- First simplify RHS tensor product scalar to single smul
  rw [TensorProduct.smul_tmul_smul]
  congr 1
  rw [← map_mul]
  congr 1
  show (f (eigA i * eigB j) : ℝ) = (f (eigA i) : ℝ) * (f (eigB j) : ℝ)
  simp only [f]
  rw [← NNReal.coe_mul]
  congr 1
  rw [Real.toNNReal_mul (heigA_nonneg i), NNReal.mul_rpow]

end TensorCFC


