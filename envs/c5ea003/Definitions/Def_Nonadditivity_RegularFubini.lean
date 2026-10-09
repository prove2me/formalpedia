-- Prove2me | Definitions.Def_Nonadditivity_RegularFubini
-- name    : Nonadditivity_RegularFubini
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:40:25.755267+00:00
-- url     : https://prove2.me/theorems/80ffcabe-c4b2-4e49-9826-b5900d06717b
-- title:
--   Fubini isometries for vector valued regular Hilbert spaces
-- statement:
--   Currying and uncurrying give an actual complex linear isometric equivalence between $\ell^2(F\times G;E)$ and $\ell^2(F;\ell^2(G;E))$. For products of free groups, splitting the first factor and its branch index transports the coefficient polynomial into diagonal and off-diagonal components. The supplied identities and norm estimates justify that transport and the coordinatewise operator lifts.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/RegularFubini.lean#L25-L285

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_CollinsYoun
import Definitions.Def_Nonadditivity_CollinsYounTensor
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_FreeCreation
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_Linearization
import Definitions.Def_Nonadditivity_MatrixRegularRestriction
import Definitions.Def_Nonadditivity_RegularCoefficientEnergy
import Definitions.Def_Nonadditivity_RegularRestriction
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/



/-! # Fubini isometry for the actual regular representation

Square-summable functions on a product group are identified isometrically
with square-summable Hilbert-valued functions on its first factor. This
identification intertwines the actual bounded regular polynomials.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.RegularFubini

open scoped BigOperators ENNReal
open RegularCoefficientEnergy (VectorHilbert)

variable {F G E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A square-summable slice at the first coordinate. -/
def slice (f : VectorHilbert (F × G) E) (x : F) : VectorHilbert G E :=
  ⟨fun y => f (x, y), by
    apply memℓp_gen
    exact (f.property.summable (by norm_num)).prod_factor x⟩

omit [NormedSpace ℂ E] in
@[simp] theorem slice_apply (f : VectorHilbert (F × G) E) (x : F) (y : G) :
    slice f x y = f (x, y) := rfl

/-- Currying preserves square summability, including the outer summation. -/
def curry (f : VectorHilbert (F × G) E) : VectorHilbert F (VectorHilbert G E) :=
  ⟨slice f, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    have hs : Summable (fun p : F × G => ‖f p‖ ^ 2) := by
      simpa using f.property.summable (by norm_num)
    convert hs.prod using 1
    funext x
    exact MatrixRegularRestriction.norm_sq (slice f x)⟩

omit [NormedSpace ℂ E] in
@[simp] theorem curry_apply (f : VectorHilbert (F × G) E) (x : F) (y : G) :
    curry f x y = f (x, y) := rfl

/-- Uncurrying preserves square summability by the nonnegative Fubini theorem. -/
def uncurry (f : VectorHilbert F (VectorHilbert G E)) : VectorHilbert (F × G) E :=
  ⟨fun p => f p.1 p.2, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    constructor
    · intro x
      simpa using (f x).property.summable (by norm_num)
    · have hs : Summable (fun x => ‖f x‖ ^ 2) := by
        simpa using f.property.summable (by norm_num)
      convert hs using 1
      funext x
      exact (MatrixRegularRestriction.norm_sq (f x)).symm⟩

omit [NormedSpace ℂ E] in
@[simp] theorem uncurry_apply (f : VectorHilbert F (VectorHilbert G E)) (x : F) (y : G) :
    uncurry f (x, y) = f x y := rfl

omit [NormedSpace ℂ E] in
theorem curry_norm (f : VectorHilbert (F × G) E) : ‖curry f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [MatrixRegularRestriction.norm_sq, MatrixRegularRestriction.norm_sq]
  have hs : Summable (fun p : F × G => ‖f p‖ ^ 2) := by
    simpa using f.property.summable (by norm_num)
  rw [hs.tsum_prod]
  apply tsum_congr
  intro x
  exact MatrixRegularRestriction.norm_sq (curry f x)

/-- The actual complex linear isometric equivalence implementing Fubini. -/
def curryIsometry : VectorHilbert (F × G) E ≃ₗᵢ[ℂ]
    VectorHilbert F (VectorHilbert G E) where
  toFun := curry
  invFun := uncurry
  left_inv := by intro f; ext p; rfl
  right_inv := by intro f; ext x y; rfl
  map_add' := by intro f g; ext x y; rfl
  map_smul' := by intro z f; ext x y; rfl
  norm_map' := curry_norm

@[simp] theorem curryIsometry_apply (f : VectorHilbert (F × G) E) (x : F) (y : G) :
    curryIsometry f x y = f (x, y) := rfl

@[simp] theorem curryIsometry_symm_apply (f : VectorHilbert F (VectorHilbert G E))
    (x : F) (y : G) : curryIsometry.symm f (x, y) = f x y := rfl

section Group

variable [Group F] [Group G]



/-- Exact polynomial intertwining for arbitrary finite scalar coefficients. -/
theorem curry_polynomial {I : Type*} [Fintype I] (u : I → F) (v : I → G)
    (a : I → ℂ) (f : FreeModel.Hilbert (F × G)) :
    curry ((∑ i, a i • FreeModel.leftRegular (u i, v i)) f) =
      MatrixRegularRestriction.coefficientPolynomial u
        (fun i => a i • FreeModel.leftRegular (v i)) (curry f) := by
  ext x y
  simp only [curry_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    MatrixRegularRestriction.coefficientPolynomial_apply, FreeModel.leftRegular_apply]
  rfl

/-- The scalar regular norm on a product group is exactly the corresponding
operator-coefficient regular norm on the first group. -/
theorem polynomial_norm_eq {I : Type*} [Fintype I] (u : I → F) (v : I → G)
    (a : I → ℂ) :
    ‖∑ i, a i • FreeModel.leftRegular (u i, v i)‖ =
      ‖MatrixRegularRestriction.coefficientPolynomial u
        (fun i => a i • FreeModel.leftRegular (v i))‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    rw [← curry_norm, curry_polynomial]
    exact ((MatrixRegularRestriction.coefficientPolynomial u
      (fun i => a i • FreeModel.leftRegular (v i))).le_opNorm (curry f)).trans_eq
      (by rw [curry_norm])
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    obtain ⟨g, rfl⟩ := (curryIsometry (F := F) (G := G) (E := ℂ)).surjective f
    change ‖MatrixRegularRestriction.coefficientPolynomial u
      (fun i => a i • FreeModel.leftRegular (v i)) (curry g)‖ ≤
        ‖∑ i, a i • FreeModel.leftRegular (u i, v i)‖ * ‖curry g‖
    rw [← curry_polynomial, curry_norm, curry_norm]
    exact (∑ i, a i • FreeModel.leftRegular (u i, v i)).le_opNorm g

end Group

section OperatorCoefficients

variable {α H : Type*} [Fintype α] [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Amplifying a coefficient operator on an ℓ² index set cannot increase its norm. -/
theorem liftOperator_norm_le (T : H →L[ℂ] H) :
    ‖RegularCoefficientEnergy.liftOperator (G := F) T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  exact RegularCoefficientEnergy.liftFunction_norm_le T

/-- The diagonal terms are exactly one amplified sum of coefficient operators. -/
theorem coefficientPolynomial_diagonal_split [Group F] [DecidableEq α]
    (u : α → F) (B : α → α → H →L[ℂ] H) :
    MatrixRegularRestriction.coefficientPolynomial
      (fun p : α × α => (u p.1)⁻¹ * u p.2) (fun p => B p.1 p.2) =
      RegularCoefficientEnergy.liftOperator (∑ i, B i i) +
        MatrixRegularRestriction.coefficientPolynomial
          (fun p : α × α => (u p.1)⁻¹ * u p.2)
          (fun p => if p.1 = p.2 then 0 else B p.1 p.2) := by
  ext f x
  simp only [MatrixRegularRestriction.coefficientPolynomial_apply,
    ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply,
    RegularCoefficientEnergy.liftOperator_apply, ContinuousLinearMap.sum_apply,
    Fintype.sum_prod_type]
  have hd : (∑ i, B i i (f x)) =
      ∑ i, ∑ j, if i = j then B i j (f (((u i)⁻¹ * u j)⁻¹ * x)) else 0 := by
    simp
  rw [hd, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j <;> simp [hij]

end OperatorCoefficients

section HilbertCoefficients

variable {α H : Type*} [Fintype α] [DecidableEq α] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A general operator-valued length-two polynomial separates into its exact
diagonal sum and an off-diagonal term bounded by three coefficient energies. -/
theorem coefficientPolynomial_norm_le_diagonal_offDiagonal
    (B : α → α → H →L[ℂ] H) :
    ‖MatrixRegularRestriction.coefficientPolynomial
      (fun p : α × α => (FreeGroup.of p.1)⁻¹ * FreeGroup.of p.2) (fun p => B p.1 p.2)‖ ≤
      ‖∑ i, B i i‖ +
        3 * Real.sqrt (∑ i, ∑ j, if i = j then 0 else ‖B i j‖ ^ 2) := by
  rw [coefficientPolynomial_diagonal_split]
  refine (norm_add_le (RegularCoefficientEnergy.liftOperator (∑ i, B i i))
    (MatrixRegularRestriction.coefficientPolynomial
      (fun p : α × α => (FreeGroup.of p.1)⁻¹ * FreeGroup.of p.2)
      (fun p => if p.1 = p.2 then 0 else B p.1 p.2))).trans ?_
  apply add_le_add (liftOperator_norm_le _)
  have he (C : α → α → H →L[ℂ] H) :
      MatrixRegularRestriction.coefficientPolynomial
        (fun p : α × α => (FreeGroup.of p.1)⁻¹ * FreeGroup.of p.2) (fun p => C p.1 p.2) =
        CollinsYounTensor.localPolynomial C := by
    ext f x
    simp [MatrixRegularRestriction.coefficientPolynomial_apply,
      CollinsYounTensor.localPolynomial_apply, Fintype.sum_prod_type]
  rw [he (fun i j => if i = j then 0 else B i j)]
  have hb := CollinsYounTensor.local_polynomial_norm_le_three_coeff
    (fun i j => if i = j then 0 else B i j) (fun i => by simp)
  convert hb using 1
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j <;> simp [hij]

end HilbertCoefficients

section Successor

open FreeModel

/-- Splitting the first coordinate of a tuple of free-group elements. -/
def groupSuccEquiv (K n : ℕ) : ProductFreeGroup K (n+1) ≃*
    FreeGroup (Fin K) × ProductFreeGroup K n where
  toFun g := (g 0, fun j => g j.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv g := by ext j; exact Fin.cases rfl (fun _ => rfl) j
  right_inv p := by ext <;> rfl
  map_mul' g h := rfl

 def branchSuccEquiv (K n : ℕ) : Branch K (n+1) ≃ Fin K × Branch K n where
  toFun a := (a 0, fun j => a j.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv a := by ext j; exact Fin.cases rfl (fun _ => rfl) j
  right_inv p := by ext <;> rfl

 theorem sum_branch_succ {K n : ℕ} {M : Type*} [AddCommMonoid M]
    (f : Branch K (n+1) → M) :
    (∑ a, f a) = ∑ i, ∑ a, f (Fin.cons i a) := by
  rw [← (Nonadditivity.RegularFubini.branchSuccEquiv K n).symm.sum_comp]
  exact Fintype.sum_prod_type _

@[simp] theorem groupSuccEquiv_branchWord_cons {K n : ℕ} (i : Fin K) (a : Branch K n) :
    groupSuccEquiv K n (branchWord (Fin.cons i a)) = (FreeGroup.of i, branchWord a) := by
  rfl

/-- Exact first-coordinate recurrence for the unnormalized product polynomial. -/
theorem polynomial_succ_norm_eq {K n : ℕ}
    (A : Matrix (Branch K (n+1)) (Branch K (n+1)) ℂ) :
    ‖∑ a, ∑ b, A a b • leftRegular ((branchWord a)⁻¹ * branchWord b)‖ =
      ‖MatrixRegularRestriction.coefficientPolynomial
        (fun p : Fin K × Fin K => (FreeGroup.of p.1)⁻¹ * FreeGroup.of p.2)
        (fun p => ∑ a : Branch K n, ∑ b : Branch K n,
          A (Fin.cons p.1 a) (Fin.cons p.2 b) •
            leftRegular ((branchWord a)⁻¹ * branchWord b))‖ := by
  have he := RegularRestriction.regularPolynomial_equiv_norm_eq
    (groupSuccEquiv K n)
    (fun p : Branch K (n+1) × Branch K (n+1) => (branchWord p.1)⁻¹ * branchWord p.2)
    (fun p => A p.1 p.2)
  simp only [RegularRestriction.regularPolynomial, Fintype.sum_prod_type] at he
  rw [← he]
  have hs : (∑ a, ∑ b, A a b •
      leftRegular (groupSuccEquiv K n ((branchWord a)⁻¹ * branchWord b))) =
      ∑ p : (Fin K × Branch K n) × (Fin K × Branch K n),
        A (Fin.cons p.1.1 p.1.2) (Fin.cons p.2.1 p.2.2) •
          leftRegular ((FreeGroup.of p.1.1)⁻¹ * FreeGroup.of p.2.1,
            (branchWord p.1.2)⁻¹ * branchWord p.2.2) := by
    rw [Nonadditivity.RegularFubini.sum_branch_succ]
    simp_rw [Nonadditivity.RegularFubini.sum_branch_succ]
    simp only [Fintype.sum_prod_type, map_mul, map_inv, groupSuccEquiv_branchWord_cons,
      Prod.inv_mk, Prod.mk_mul_mk]
  rw [hs, polynomial_norm_eq]
  congr 1
  ext f x y
  simp only [MatrixRegularRestriction.coefficientPolynomial_apply,
    Fintype.sum_prod_type, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, leftRegular_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

end Successor

end Nonadditivity.RegularFubini


