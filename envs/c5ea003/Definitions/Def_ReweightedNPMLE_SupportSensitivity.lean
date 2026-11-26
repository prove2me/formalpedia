-- Prove2me | Definitions.Def_ReweightedNPMLE_SupportSensitivity
-- name    : ReweightedNPMLE_SupportSensitivity
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:22:58.437643+00:00
-- url     : https://prove2.me/theorems/006c5430-6cb8-5fd9-b732-3c7a9f3ce183
-- title:
--   Mass-preserving relative fitted-value tangent spaces
-- statement:
--   For \(k\) dictionary vectors \(A_j\in\mathbb R^n\), fitted values \(v\), and weights \(w\), let
--   \[
--   Z_k=\{c\in\mathbb R^k:\sum_jc_j=0\},\qquad
--   (R_{A,v}c)_i=\frac{\sum_jc_jA_{j,i}}{v_i},
--   \quad
--   (\widetilde R_{A,v,w}c)_i=\sqrt{w_i}(R_{A,v}c)_i.
--   \]
--   The coefficient-total map is \(c\mapsto\sum_jc_j\), and \(Z_k\) is its kernel. Restricting \(\widetilde R\) to \(Z_k\) gives the mass-preserving relative map; its image is the weighted relative tangent subspace of Euclidean \(\mathbb R^n\). For any Euclidean subspace \(S\), choose an orthonormal basis and place its coordinate vectors in an \(n\times\dim S\) matrix. A further construction regards any matrix column as a Euclidean vector. These objects express support perturbations and their dimensions in matrix form.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/SupportSensitivity.lean#L25-L245

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Finite-support tangent directions

This file formalizes the algebraic half of the paper's matrix-sensitivity
lemma.  Mass-preserving perturbations of a `k`-atom optimizer form a
`(k - 1)`-dimensional coefficient space.  A linearly independent evaluation
dictionary maps that space injectively to relative fitted-value directions.
After the square-root weight scaling, these directions remain
`(k - 1)`-dimensional, are orthogonal to the square-root weight vector by the
likelihood contact equations, and admit an explicit orthonormal matrix.
-/

open Set
open scoped BigOperators Matrix

namespace ReweightedNPMLE

def coefficientTotalLinearMap (k : ℕ) : (Fin k → ℝ) →ₗ[ℝ] ℝ where
  toFun c := ∑ j, c j
  map_add' c d := by simp [Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.mul_sum]



def zeroSumCoefficients (k : ℕ) : Submodule ℝ (Fin k → ℝ) :=
  LinearMap.ker (coefficientTotalLinearMap k)







noncomputable def relativeDictionaryMap {k n : ℕ} (A : Fin k → Fin n → ℝ)
    (v : Fin n → ℝ) : (Fin k → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun c i := (∑ j, c j * A j i) / v i
  map_add' c d := by
    funext i
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' r c := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    calc
      (∑ x, r * c x * A x i) / v i =
          (r * ∑ x, c x * A x i) / v i := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = r * ((∑ j, c j * A j i) / v i) := by ring















noncomputable def weightedRelativeDictionaryMap {k n : ℕ}
    (A : Fin k → Fin n → ℝ) (v w : Fin n → ℝ) :
    (Fin k → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun c := WithLp.toLp 2 fun i ↦
    Real.sqrt (w i) * relativeDictionaryMap A v c i
  map_add' c d := by
    apply PiLp.ext
    intro i
    change Real.sqrt (w i) * relativeDictionaryMap A v (c + d) i = _
    rw [map_add]
    simp [Pi.add_apply]
    ring
  map_smul' r c := by
    apply PiLp.ext
    intro i
    change Real.sqrt (w i) * relativeDictionaryMap A v (r • c) i = _
    rw [map_smul]
    simp [Pi.smul_apply]
    ring

noncomputable def weightedMassPreservingRelativeMap {k n : ℕ}
    (A : Fin k → Fin n → ℝ) (v w : Fin n → ℝ) :
    zeroSumCoefficients k →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (weightedRelativeDictionaryMap A v w).comp (zeroSumCoefficients k).subtype

noncomputable def weightedRelativeTangentSpace {k n : ℕ}
    (A : Fin k → Fin n → ℝ) (v w : Fin n → ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  LinearMap.range (weightedMassPreservingRelativeMap A v w)







noncomputable def submoduleOrthonormalMatrix {n : ℕ}
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    Matrix (Fin n) (Fin (Module.finrank ℝ S)) ℝ :=
  fun i j ↦ ((stdOrthonormalBasis ℝ S j : S) : Fin n → ℝ) i



noncomputable def matrixColumnEuclidean {n m : ℕ}
    (V : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ V i j)



















end ReweightedNPMLE


