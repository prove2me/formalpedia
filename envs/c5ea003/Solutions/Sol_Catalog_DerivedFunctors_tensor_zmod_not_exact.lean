-- Prove2me | solution 1 for Catalog.DerivedFunctors.tensor_zmod_not_exact
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:06:10.941592+00:00
-- url     : https://prove2.me/submissions/4561819c-0114-4ab0-a060-c0b6a81fa2d1

-- Sol generated from Algebra/DerivedFunctors/UniversalCoefficients.lean
import Mathlib
import Definitions.Def_Algebra_DerivedFunctors_UniversalCoefficients

/-!
# Universal coefficients: flat coefficients and the failure of flatness

The universal coefficient theorem for homology relates `H_n(C ⊗ G)` with `H_n(C) ⊗ G` and a
correction term `Tor₁(H_{n-1}(C), G)`. This file formalises the two extreme phenomena:

* `Catalog.DerivedFunctors.homologyTensorFlatIso`: **the universal coefficient theorem with flat
  coefficients**. If `G` is a flat `R`-module, the correction term disappears and
  `H_n(C ⊗ G) ≅ H_n(C) ⊗ G` for every complex `C` of `R`-modules (any complex shape).
  A `LinearEquiv` version is `Catalog.DerivedFunctors.homologyTensorFlatLinearEquiv`, and
  `Catalog.DerivedFunctors.homology_tensor_eq_zero_of_flat` records that tensoring with a flat
  module preserves acyclicity.

* `Catalog.DerivedFunctors.tensor_zmod_not_exact`: for non-flat coefficients the correction term is
  really needed. The short complex `0 → ℤ --(·k)--> ℤ` of `ℤ`-modules is exact (multiplication by
  `k ≠ 0` is injective, i.e. `H₁` of the two-term complex vanishes), yet after tensoring with
  `ZMod k` (`k ≥ 2`) it is no longer exact: a nonzero class survives, which is exactly the
  `Tor₁(ZMod k, ZMod k)`-term of the universal coefficient sequence.
-/

universe u v

open CategoryTheory MonoidalCategory Limits HomologicalComplex
open scoped TensorProduct

open Catalog.DerivedFunctors


variable {R : Type u} [CommRing R] (G : ModuleCat.{u} R) [Module.Flat R G]
  {ι : Type v} {c : ComplexShape ι}











open Catalog.DerivedFunctors in
theorem solution(k : ℕ) (hk : 2 ≤ k) :
    ¬ ((mulShortComplex k).map (tensorLeft (ModuleCat.of ℤ (ZMod k)))).Exact := by
  intro hex
  rw [ShortComplex.moduleCat_exact_iff] at hex
  set x : (ZMod k) ⊗[ℤ] ℤ := (1 : ZMod k) ⊗ₜ[ℤ] (1 : ℤ) with hxdef
  have hgx : (ConcreteCategory.hom ((mulShortComplex k).map
      (tensorLeft (ModuleCat.of ℤ (ZMod k)))).g) x = 0 := by
    show ((ModuleCat.of ℤ (ZMod k)) ◁ (ModuleCat.ofHom ((k : ℤ) • LinearMap.id)))
      ((1 : ZMod k) ⊗ₜ[ℤ] (1 : ℤ)) = 0
    rw [ModuleCat.MonoidalCategory.whiskerLeft_apply]
    show (1 : ZMod k) ⊗ₜ[ℤ] ((k : ℤ) • (1 : ℤ)) = 0
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    have hz : ((k : ℤ) • (1 : ZMod k)) = 0 := by simp [zsmul_eq_mul]
    rw [hz, TensorProduct.zero_tmul]
  obtain ⟨y, hy⟩ := hex x hgx
  have hf : (ConcreteCategory.hom ((mulShortComplex k).map
      (tensorLeft (ModuleCat.of ℤ (ZMod k)))).f) y = 0 := by
    simp [mulShortComplex]; rfl
  have hx0 : x = 0 := hy.symm.trans hf
  have h1 : (TensorProduct.rid ℤ (ZMod k)) ((1 : ZMod k) ⊗ₜ[ℤ] (1 : ℤ)) = 0 := by
    rw [← hxdef, hx0]; simp
  simp at h1
  haveI : Fact (1 < k) := ⟨by omega⟩
  exact one_ne_zero h1
