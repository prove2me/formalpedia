-- Prove2me | Definitions.Def_Nonadditivity_PolynomialReduction
-- name    : Nonadditivity_PolynomialReduction
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:43:11.55283+00:00
-- url     : https://prove2.me/theorems/ff4e14ef-2976-49ee-bd0b-6541422b9d48
-- title:
--   Finite matrix polynomials and a constructed Gram-factorization step
-- statement:
--   For a group $G$, a matrix-polynomial package $P$ records a finite nonempty coefficient index set $I$, a finite summation support $S\subseteq G$, and a coefficient map $a:G\to M_I(\mathbb C)$. Its finite evaluation at a unitary representation $\pi:G\to U(d)$ is
--   $$P(\pi)=\sum_{g\in S}a(g)\otimes\pi(g).$$
--   The bundle also defines evaluation at the infinite regular representation and the coefficient map set to zero outside $S$. For a finite set $S'$ containing the identity, a constructed Gram-factorization step uses coefficient space $S'\times(I\sqcup I)$, with
--   $$\dim\operatorname{Coeff}(\operatorname{step}_{S'}P)=2|S'|\,|I|.$$
--   Its finite and regular evaluations are identified with the corresponding padded Hermitian-dilation polynomials. For free-group words, prefix and suffix operations define the finite splitting support $\{1\}\cup\{\operatorname{prefix}_r(w)^{-1}:w\in S\}\cup\{\operatorname{suffix}_r(w):w\in S\}$. These constructions keep coefficient spaces, supports, and evaluations explicit through the reduction.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/PolynomialReduction.lean#L27-L171

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_FiniteSetFactorization
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_Linearization
import Definitions.Def_Nonadditivity_MatrixRegularRestriction
import Definitions.Def_Nonadditivity_RegularCoefficientEnergy
import Definitions.Def_Nonadditivity_RegularDilation
import Definitions.Def_Nonadditivity_RegularFactorization
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
import Mathlib.GroupTheory.FreeGroup.Reduce
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




/-! # Constructed polynomial shortening

The support at each step is obtained by cutting the actual reduced words. The
coefficient matrices are the positive-Gram factors, evaluated simultaneously
at every finite representation and at the infinite regular representation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Nonadditivity.PolynomialReduction
open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker
open FiniteSetFactorization RegularCoefficientEnergy

section Support
variable {α : Type} [DecidableEq α]

def firstHalf (r : ℕ) (w : FreeGroup α) : FreeGroup α :=
  FreeGroup.mk (w.toWord.take r)

def suffix (r : ℕ) (w : FreeGroup α) : FreeGroup α :=
  FreeGroup.mk (w.toWord.drop r)







/-- The actual two halves of each supported word, with the first half inverted. -/
def splitSupport (T : Finset (FreeGroup α)) (r : ℕ) : Finset (FreeGroup α) :=
  insert 1 ((T.image fun w => (firstHalf r w)⁻¹) ∪ T.image (suffix r))

@[simp] theorem one_mem_splitSupport (T : Finset (FreeGroup α)) (r : ℕ) :
    (1 : FreeGroup α) ∈ splitSupport T r := by simp [splitSupport]






end Support

/-- A literal finite matrix-coefficient polynomial, with its coefficient space. -/
structure Polynomial (G : Type*) where
  Index : Type
  fintype : Fintype Index
  decEq : DecidableEq Index
  nonempty : Nonempty Index
  support : Finset G
  coefficient : G → Matrix Index Index ℂ

attribute [instance] Polynomial.fintype Polynomial.decEq Polynomial.nonempty

namespace Polynomial
variable {G : Type} [Group G] [DecidableEq G]

def finiteEval (P : Polynomial G) {ν : Type*} [Fintype ν] [DecidableEq ν]
    (π : G →* unitary (Matrix ν ν ℂ)) : Matrix (P.Index × ν) (P.Index × ν) ℂ :=
  ∑ w ∈ P.support, P.coefficient w ⊗ₖ (π w : Matrix ν ν ℂ)

def regularEval (P : Polynomial G) := regularPolynomial P.support P.coefficient

def normalizedCoefficient (P : Polynomial G) (w : G) : Matrix P.Index P.Index ℂ :=
  if w ∈ P.support then P.coefficient w else 0





/-- A genuine step of Gram factorization, including the enlarged coefficient space. -/
def step (P : Polynomial G) (S : Finset G) (hS : (1:G) ∈ S) : Polynomial G where
  Index := Support S × (P.Index ⊕ P.Index)
  fintype := inferInstance
  decEq := inferInstance
  nonempty := ⟨⟨⟨1,hS⟩, Sum.inl (Classical.choice P.nonempty)⟩⟩
  support := S
  coefficient := RegularFactorization.paddedCoefficients S hS
    (dilationCoefficient P.normalizedCoefficient)

@[simp] theorem step_dimension (P : Polynomial G) (S : Finset G) (hS : (1:G) ∈ S) :
    Fintype.card (P.step S hS).Index = 2 * S.card * Fintype.card P.Index := by
  simp [step, Nat.mul_add]
  ring



@[simp] theorem step_finiteEval (P : Polynomial G) (S : Finset G) (hS : (1:G) ∈ S)
    {ν : Type*} [Fintype ν] [DecidableEq ν]
    (π : G →* unitary (Matrix ν ν ℂ)) :
    (P.step S hS).finiteEval π =
      paddedPolynomial S hS (dilationCoefficient P.normalizedCoefficient) π := by
  unfold finiteEval step paddedPolynomial
  rw [← Finset.sum_coe_sort S]
  apply Finset.sum_congr rfl
  intro g hg
  simp [RegularFactorization.paddedCoefficients, g.property]

@[simp] theorem step_regularEval (P : Polynomial G) (S : Finset G) (hS : (1:G) ∈ S) :
    (P.step S hS).regularEval =
      RegularFactorization.padded S hS (dilationCoefficient P.normalizedCoefficient) :=
  (RegularFactorization.padded_eq_regularPolynomial S hS _).symm











section FreeGroup
variable {α : Type} [DecidableEq α]

























end FreeGroup

end Polynomial
end Nonadditivity.PolynomialReduction


