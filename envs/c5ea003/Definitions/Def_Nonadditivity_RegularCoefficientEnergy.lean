-- Prove2me | Definitions.Def_Nonadditivity_RegularCoefficientEnergy
-- name    : Nonadditivity_RegularCoefficientEnergy
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:35:48.289097+00:00
-- url     : https://prove2.me/theorems/5720f46b-571d-4472-ab39-39242ade58ef
-- title:
--   Coefficient operators on vector valued square summable functions
-- statement:
--   This bundle defines $\ell^2(G;E)$ for an index type $G$ and a complex Hilbert coefficient space $E$, together with reindexing isometries and the coordinatewise lift of a bounded operator on $E$. The finite coefficient-space specialization is $E=\mathbb C^I$ with its Euclidean norm. The supplied energy estimates justify square summability and boundedness of these operations. Bounded regular shifts and matrix coefficient operators define the finite matrix-valued polynomial $\sum_{w\in S}\widetilde{c_w}\lambda_w$ on $\ell^2(G;\mathbb C^I)$.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/RegularCoefficientEnergy.lean#L25-L141

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_Linearization
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
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
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/





/-! # Coefficient energy of an actual regular-representation polynomial

Evaluation on a vector supported at the group identity isolates every
coefficient into a distinct orthogonal coordinate of the vector-valued
square-summable Hilbert space.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.RegularCoefficientEnergy

open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder

abbrev VectorHilbert (G E : Type*) [NormedAddCommGroup E] := lp (fun _ : G => E) 2

section Lift

variable {G E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 theorem square_bound (T : E →L[ℂ] E) (x : E) :
    ‖T x‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖x‖ ^ 2 := by
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm x) 2

/-- Apply a bounded coefficient operator independently at every coordinate. -/
def liftFunction (T : E →L[ℂ] E) (f : VectorHilbert G E) : VectorHilbert G E :=
  ⟨fun g => T (f g), by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun g => Nonadditivity.RegularCoefficientEnergy.square_bound T (f g))
      ?_
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (f.property.summable (by norm_num)).mul_left (‖T‖ ^ 2)⟩

@[simp] theorem liftFunction_apply (T : E →L[ℂ] E) (f : VectorHilbert G E) (g : G) :
    liftFunction T f g = T (f g) := rfl

theorem liftFunction_norm_le (T : E →L[ℂ] E) (f : VectorHilbert G E) :
    ‖liftFunction T f‖ ≤ ‖T‖ * ‖f‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  calc
    (∑' g, ‖T (f g)‖ ^ 2) ≤ ∑' g, ‖T‖ ^ 2 * ‖f g‖ ^ 2 := by
      apply Summable.tsum_le_tsum
      · exact fun g => Nonadditivity.RegularCoefficientEnergy.square_bound T (f g)
      · simpa only [liftFunction_apply, ENNReal.toReal_ofNat, Real.rpow_two] using
          (liftFunction T f).property.summable (by norm_num)
      · simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          (f.property.summable (by norm_num)).mul_left (‖T‖ ^ 2)
    _ = (‖T‖ * ‖f‖) ^ 2 := by
      rw [tsum_mul_left, mul_pow]
      congr 1
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.norm_rpow_eq_tsum (by norm_num) f).symm

def liftOperator (T : E →L[ℂ] E) : VectorHilbert G E →L[ℂ] VectorHilbert G E :=
  LinearMap.mkContinuous
    { toFun := liftFunction T
      map_add' := by intro f h; ext g; simp
      map_smul' := by intro c f; ext g; simp }
    ‖T‖ (liftFunction_norm_le T)

@[simp] theorem liftOperator_apply (T : E →L[ℂ] E) (f : VectorHilbert G E) (g : G) :
    liftOperator T f g = T (f g) := rfl



/-- Coordinate permutations are actual Hilbert-space isometries. -/
def reindexFunction (e : G ≃ G) (f : VectorHilbert G E) : VectorHilbert G E :=
  ⟨fun g => f (e g), by
    apply memℓp_gen
    exact (e.summable_iff
      (f := fun g : G => ‖f g‖ ^ (2 : ℝ≥0∞).toReal)).mpr
      (f.property.summable (by norm_num))⟩

def reindexIsometry (e : G ≃ G) : VectorHilbert G E ≃ₗᵢ[ℂ] VectorHilbert G E where
  toFun := reindexFunction e
  invFun := reindexFunction e.symm
  left_inv := by intro f; ext g; simp [reindexFunction]
  right_inv := by intro f; ext g; simp [reindexFunction]
  map_add' := by intro f h; ext g; rfl
  map_smul' := by intro c f; ext g; rfl
  norm_map' := by
    intro f
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    exact congrArg (fun t : ℝ => t ^ (1 / (2 : ℝ≥0∞).toReal))
      (e.tsum_eq (fun g => ‖f g‖ ^ (2 : ℝ≥0∞).toReal))

end Lift

section Polynomial

variable {G ι : Type*} [Group G] [DecidableEq G] [Fintype ι] [DecidableEq ι]

abbrev CoefficientSpace (ι : Type*) [Fintype ι] := EuclideanSpace ℂ ι
abbrev Hilbert (G ι : Type*) [Fintype ι] := VectorHilbert G (CoefficientSpace ι)

def coefficientOperator (A : Matrix ι ι ℂ) : CoefficientSpace ι →L[ℂ] CoefficientSpace ι :=
  Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A

def leftRegular (g : G) : Hilbert G ι →L[ℂ] Hilbert G ι :=
  (reindexIsometry (E := CoefficientSpace ι) (Equiv.mulLeft g⁻¹)).toLinearIsometry.toContinuousLinearMap

omit [DecidableEq G] [DecidableEq ι] in
@[simp] theorem leftRegular_apply (g : G) (f : Hilbert G ι) (h : G) :
    leftRegular g f h = f (g⁻¹ * h) := rfl

omit [DecidableEq ι] in
theorem leftRegular_single (g h : G) (x : CoefficientSpace ι) :
    leftRegular g (lp.single 2 h x) = lp.single 2 (g * h) x := by
  ext z
  simp only [leftRegular_apply, lp.single_apply, Pi.single_apply]
  have heq : g⁻¹ * z = h ↔ z = g * h := by
    constructor
    · intro hz
      have hm := congrArg (fun t => g * t) hz
      simpa [mul_assoc] using hm
    · intro hz
      rw [hz]
      simp
  simp only [heq]

/-- The literal finite polynomial `∑ c_w ⊗ λ(w)`, realized on vector-valued ℓ². -/
def regularPolynomial (S : Finset G) (c : G → Matrix ι ι ℂ) : Hilbert G ι →L[ℂ] Hilbert G ι :=
  ∑ w ∈ S, (liftOperator (coefficientOperator (c w))).comp (leftRegular w)











end Polynomial

end Nonadditivity.RegularCoefficientEnergy


