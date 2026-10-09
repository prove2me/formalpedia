-- Prove2me | Definitions.Def_Nonadditivity_RegularFactorization
-- name    : Nonadditivity_RegularFactorization
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:41:36.651974+00:00
-- url     : https://prove2.me/theorems/a8873c3a-d7a4-4f51-8a2e-21fadf59e298
-- title:
--   Pointwise matrix lifts and regular polynomial factorization data
-- statement:
--   A continuous linear map lifts pointwise to vector-valued $\ell^2$ functions, with its norm bounded by the original operator norm. Matrix lifts preserve the zero, identity, addition, scalar multiplication, composition, and adjoint operations used by block calculations. Combining these lifts with group shifts defines matrix-coefficient terms and polynomial evaluations. The interface also constructs padded coefficients and identifies their regular polynomial with the specified factorization expression.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/RegularFactorization.lean#L34-L397

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_FiniteSetFactorization
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_Linearization
import Definitions.Def_Nonadditivity_MatrixRegularRestriction
import Definitions.Def_Nonadditivity_RegularCoefficientEnergy
import Definitions.Def_Nonadditivity_RegularDilation
import Definitions.Def_Nonadditivity_RegularRestriction
import Definitions.Def_Nonadditivity_RegularShiftedDilation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
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




/-! # Finite-set factorization at the actual infinite regular representation

Rectangular coefficient matrices act pointwise on vector-valued square-summable
functions. Their lifted adjoints and products agree with the literal matrix
operations. This permits evaluation of the same positive Gram matrix used for
finite-dimensional representations at the infinite left regular representation.

The constructed square factor has exactly squared norm `‖P(λ)‖ + θ`, with the
same coefficients and scalar as its finite-representation evaluation. The scalar
bound `θ ≤ |S| ‖P(λ)‖` and both norm identities therefore yield the concrete
backward relative-error bound `e(P) ≤ 6 |S| e(Q)`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Nonadditivity.RegularFactorization
open RegularCoefficientEnergy
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder Kronecker

section Lift
variable {G E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def liftFunction (T : E →L[ℂ] F) (f : VectorHilbert G E) : VectorHilbert G F :=
  ⟨fun g => T (f g), by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    refine Summable.of_nonneg_of_le (f := fun g => ‖T‖ ^ 2 * ‖f g‖ ^ 2)
      (fun _ => sq_nonneg _) (fun g => ?_) ?_
    · simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm (f g)) 2
    · simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (f.property.summable (by norm_num)).mul_left (‖T‖ ^ 2)⟩

theorem liftFunction_norm_le (T : E →L[ℂ] F) (f : VectorHilbert G E) :
    ‖liftFunction T f‖ ≤ ‖T‖ * ‖f‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  calc
    (∑' g, ‖T (f g)‖ ^ 2) ≤ ∑' g, ‖T‖ ^ 2 * ‖f g‖ ^ 2 := by
      apply Summable.tsum_le_tsum
      · intro g
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm (f g)) 2
      · simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          (liftFunction T f).property.summable (by norm_num)
      · simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          (f.property.summable (by norm_num)).mul_left (‖T‖ ^ 2)
    _ = (‖T‖ * ‖f‖) ^ 2 := by
      rw [tsum_mul_left, mul_pow]
      congr 1
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.norm_rpow_eq_tsum (by norm_num) f).symm

def lift (T : E →L[ℂ] F) : VectorHilbert G E →L[ℂ] VectorHilbert G F :=
  LinearMap.mkContinuous
    { toFun := liftFunction T
      map_add' := by intro f h; ext g; exact T.map_add _ _
      map_smul' := by intro c f; ext g; exact T.map_smul _ _ }
    ‖T‖ (liftFunction_norm_le T)

@[simp] theorem lift_apply (T : E →L[ℂ] F) (f : VectorHilbert G E) (g : G) :
    lift T f g = T (f g) := rfl

end Lift

section Matrix
variable {G ι κ μ : Type*} [Group G] [DecidableEq G]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]

def rectLift (A : Matrix ι κ ℂ) : Hilbert G κ →L[ℂ] Hilbert G ι :=
  lift (Matrix.toEuclideanLin A).toContinuousLinearMap

@[simp] theorem rectLift_apply (A : Matrix ι κ ℂ) (f : Hilbert G κ) (g : G) :
    rectLift A f g = Matrix.toEuclideanLin A (f g) := rfl

@[simp] theorem rectLift_zero : rectLift (G := G) (0 : Matrix ι κ ℂ) = 0 := by
  ext f g i
  simp [rectLift_apply]

@[simp] theorem rectLift_add (A B : Matrix ι κ ℂ) :
    rectLift (G := G) (A+B) = rectLift A + rectLift B := by
  ext f g i
  simp [rectLift_apply]

@[simp] theorem rectLift_smul (r : ℝ) (A : Matrix ι κ ℂ) :
    rectLift (G := G) (r • A) = r • rectLift A := by
  ext f g i
  simp [rectLift_apply, Matrix.smul_mulVec]

@[simp] theorem rectLift_one : rectLift (G := G) (1 : Matrix ι ι ℂ) = 1 := by
  ext f g i
  change ((1 : Matrix ι ι ℂ) *ᵥ (f g).ofLp) i = f g i
  simp

@[simp] theorem rectLift_mul (A : Matrix ι κ ℂ) (B : Matrix κ μ ℂ) :
    rectLift (G := G) (A*B) = (rectLift A).comp (rectLift B) := by
  ext f g i
  change ((A*B) *ᵥ (f g).ofLp) i = (A *ᵥ (B *ᵥ (f g).ofLp)) i
  rw [Matrix.mulVec_mulVec]

@[simp] theorem rectLift_adjoint (A : Matrix ι κ ℂ) :
    rectLift (G := G) A.conjTranspose = (rectLift A).adjoint := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro h
  rw [ContinuousLinearMap.adjoint_inner_left, lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro g
  simp only [rectLift_apply, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_left]

@[simp] theorem rectLift_sum {α : Type*} (s : Finset α) (A : α → Matrix ι κ ℂ) :
    rectLift (G := G) (∑ a ∈ s, A a) = ∑ a ∈ s, rectLift (A a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [ha, ih]

theorem rectLift_square (A : Matrix ι ι ℂ) :
    rectLift (G := G) A = liftOperator (coefficientOperator A) := by
  ext f g i
  rfl



@[simp] theorem shift_mul (g h : G) :
    (leftRegular (ι := ι) g).comp (leftRegular h) = leftRegular (g*h) := by
  ext f w i
  simp [mul_assoc]

@[simp] theorem shift_one : leftRegular (G := G) (ι := ι) 1 = 1 := by
  ext f w i
  simp

@[simp] theorem shift_adjoint (g : G) : (leftRegular (ι := ι) g).adjoint = leftRegular g⁻¹ := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro h
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro f
  change inner ℂ ((leftRegular g).adjoint (lp.single 2 h x)) f =
    inner ℂ (leftRegular g⁻¹ (lp.single 2 h x)) f
  rw [ContinuousLinearMap.adjoint_inner_left, lp.inner_single_left, leftRegular_single,
    lp.inner_single_left]
  rfl

/-- A single rectangular coefficient times a genuine regular translation. -/
def term (A : Matrix ι κ ℂ) (g : G) : Hilbert G κ →L[ℂ] Hilbert G ι :=
  (rectLift A).comp (leftRegular g)

@[simp] theorem term_add (A B : Matrix ι κ ℂ) (g : G) :
    term (A+B) g = term A g + term B g := by simp [term, ContinuousLinearMap.add_comp]

@[simp] theorem term_smul (r : ℝ) (A : Matrix ι κ ℂ) (g : G) :
    term (r • A) g = r • term A g := by simp [term, ContinuousLinearMap.smul_comp]

@[simp] theorem term_zero (g : G) : term (0 : Matrix ι κ ℂ) g = 0 := by simp [term]

@[simp] theorem term_one (g : G) : term (1 : Matrix ι ι ℂ) g = leftRegular g := by
  ext f h i
  simp [term]

@[simp] theorem term_identity (A : Matrix ι κ ℂ) : term (G := G) A 1 = rectLift A := by
  ext f h i
  simp [term]





end Matrix

section Assembly
open FiniteSetFactorization
variable {G ι : Type*} [Group G] [DecidableEq G] [Fintype ι] [DecidableEq ι]

/-- The actual column of regular translations on the given finite support. -/
def column (S : Finset G) : Hilbert G ι →L[ℂ] Hilbert G (Support S × ι) :=
  ∑ g : Support S, term (selector g).conjTranspose g.val

def evaluate (S : Finset G) (A : Matrix (Support S × ι) (Support S × ι) ℂ) :
    Hilbert G ι →L[ℂ] Hilbert G ι :=
  (column S).adjoint.comp ((rectLift A).comp (column S))



@[simp] theorem evaluate_add (S : Finset G)
    (A B : Matrix (Support S × ι) (Support S × ι) ℂ) :
    evaluate S (A+B) = evaluate S A + evaluate S B := by
  simp [evaluate, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

@[simp] theorem evaluate_smul (S : Finset G) (r : ℝ)
    (A : Matrix (Support S × ι) (Support S × ι) ℂ) :
    evaluate S (r • A) = r • evaluate S A := by
  simp [evaluate, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]











theorem polynomial_eq (S : Finset G) (c : G → Matrix ι ι ℂ) :
    regularPolynomial S c = ∑ w ∈ S, term (c w) w := by
  simp only [regularPolynomial, term, rectLift_square]



@[simp] theorem rectLift_algebraMap (r : ℝ) :
    rectLift (G := G) (algebraMap ℝ (Matrix ι ι ℂ) r) =
      algebraMap ℝ (Hilbert G ι →L[ℂ] Hilbert G ι) r := by
  simp only [Algebra.algebraMap_eq_smul_one, rectLift_smul, rectLift_one]











/-- The very same padded coefficients as in the finite representation theorem,
evaluated on actual infinite vector-valued square-summable functions. -/
def padded (S : Finset G) (hS : (1:G) ∈ S) (c : G → Matrix ι ι ℂ) :
    Hilbert G (Support S × ι) →L[ℂ] Hilbert G (Support S × ι) :=
  ∑ g : Support S, term (paddedCoefficient S hS c g) g.val

/-- Extend the constructed supported coefficients by zero to the whole group. -/
def paddedCoefficients (S : Finset G) (hS : (1:G) ∈ S) (c : G → Matrix ι ι ℂ)
    (g : G) : Matrix (Support S × ι) (Support S × ι) ℂ :=
  if hg : g ∈ S then paddedCoefficient S hS c ⟨g,hg⟩ else 0

/-- The regular factor is exactly the established literal regular-polynomial API. -/
theorem padded_eq_regularPolynomial (S : Finset G) (hS : (1:G) ∈ S)
    (c : G → Matrix ι ι ℂ) :
    padded S hS c = regularPolynomial S (paddedCoefficients S hS c) := by
  rw [polynomial_eq]
  unfold padded
  rw [← Finset.sum_coe_sort S (fun g => term (paddedCoefficients S hS c g) g)]
  apply Finset.sum_congr rfl
  intro g hg
  simp [paddedCoefficients, g.property]



















end Assembly
end Nonadditivity.RegularFactorization


