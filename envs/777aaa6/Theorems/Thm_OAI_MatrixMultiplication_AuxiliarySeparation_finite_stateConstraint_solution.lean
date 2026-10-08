-- Prove2me | Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_finite_stateConstraint_solution
-- name    : OAI.MatrixMultiplication.AuxiliarySeparation.finite_stateConstraint_solution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:13:39.384784+00:00
-- url     : https://prove2.me/theorems/3ac53607-5f69-4d4a-a400-d976441ce084
-- title:
--   A state solving finitely many supported constraints
-- statement:
--   Let $S$ be a commutative semiring with a preorder and inequality-preserving addition. Let $R:S\to\mathbb N$, $d\in S$, and $k\in\mathbb N$ satisfy $0\le x\le R(x)$ for every $x\in S$. Assume no $D,s\in S$ and positive integer $m$ satisfy $D+m+ds\le D+ks$. Let $I$ be finite, $c_i$ state constraints, and $H\subseteq S$ a finite set containing $1$ and the supports of all their integral vectors $v(c_i)$. Then there exists $f:S\to\mathbb R$ such that
--   \[
--   f(1)=1,\qquad \langle f,v(c_i)\rangle\ge0\ (i\in I),\qquad f(x)=0\ (x\notin H).
--   \]
--   The pairing is the finite sum $\langle f,v\rangle=\sum_x v(x)f(x)$. This supplies a finite-dimensional solution before all state constraints are imposed.
-- source:
--   https://prove2.me/submissions/facf5b05-d302-42c1-a107-8ff40a0c2134; OAI.MatrixMultiplication.AuxiliarySeparation.finite_stateConstraint_solution, lines 1415-1461

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.AddTorsor.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum
import Mathlib.Order.Antisymmetrization
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.MonotoneConvergence
import Definitions.Def_OAI429_OAI_LinearAlgebra_MatrixMultiplication_AuxiliarySeparation_Spectrum_Coordinates
import Definitions.Def_OAI429_OAI_LinearAlgebra_MatrixMultiplication_AuxiliarySeparation_Spectrum_StateObstruction
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_exists_normalized_nonneg_linear_of_no_nat_certificate_of_isClosed
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_isClosed_pointedCone_hull_range
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_linearCombination_finiteCoordinateState
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_no_stateConstraint_certificate
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical

theorem OAI.MatrixMultiplication.AuxiliarySeparation.finite_stateConstraint_solution.{u_1, u_2} :
    ∀ {S : Type u_1} [inst : CommSemiring S] [inst_1 : Preorder S] (R : S → ℕ) (d : S) (k : ℕ),
  (∀ (x : S), 0 ≤ x) →
    (∀ (x : S), x ≤ ↑(R x)) →
      (∀ (a b c e : S), a ≤ b → c ≤ e → a + c ≤ b + e) →
        (∀ (D s : S) (m : ℕ), 0 < m → ¬D + ↑m + d * s ≤ D + ↑k * s) →
          ∀ {I : Type u_2} [Fintype I] (cs : I → OAI.MatrixMultiplication.AuxiliarySeparation.StateConstraint S)
            (H : Finset S),
            1 ∈ H →
              (∀ (i : I),
                  (OAI.MatrixMultiplication.AuxiliarySeparation.stateConstraintVector R d k (cs i)).support ⊆ H) →
                ∃ (f : S → ℝ),
                  f 1 = 1 ∧
                    (∀ (i : I),
                        0 ≤
                          (OAI.MatrixMultiplication.AuxiliarySeparation.statePairing f)
                            (OAI.MatrixMultiplication.AuxiliarySeparation.stateConstraintVector R d k (cs i))) ∧
                      ∀ x ∉ H, f x = 0
:= by sorry
