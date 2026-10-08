-- Prove2me | Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_DeterminantFiltration_adaptedTensor_reconstruct
-- name    : OAI.MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration.adaptedTensor_reconstruct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:14:29.571932+00:00
-- url     : https://prove2.me/theorems/c71fb3cb-b4f1-4c08-9475-146cba131b6f
-- title:
--   The adapted determinant tensor reconstructs polynomial multiplication
-- statement:
--   Let $K$ be a field and $d,e\in\mathbb N$. Put $I_e=\operatorname{Fin}(e+2)\sqcup\operatorname{Fin}(e)$, and let $v_{e,j}$ be the explicit polynomial-pair vectors consisting of quotient vectors followed by determinant-kernel vectors. If $A_{d,e}$ is the adapted multiplication tensor, then for $i\in\operatorname{Fin}(d+1)$ and $j\in I_e$,
--   \[
--   \sum_{k\in I_{d+e}}A_{d,e}(i,j,k)\,v_{d+e,k}=X^i\cdot v_{e,j}.
--   \]
--   Multiplication on the right acts on both components of the polynomial pair. This verifies the coefficient formulas in the adapted coordinates.
-- source:
--   https://prove2.me/submissions/facf5b05-d302-42c1-a107-8ff40a0c2134; OAI.MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration.adaptedTensor_reconstruct, lines 13916-13949

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
import Definitions.Def_OAI429_GenericDeterminantCore
import Definitions.Def_OAI429_GenericDeterminantFiltration
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical

theorem OAI.MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration.adaptedTensor_reconstruct.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] (d e : ℕ) (i : Fin (d + 1))
  (j : OAI.MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration.Index e),
  Eq (α := OAI.MatrixMultiplication.AuxiliarySeparation.DeterminantKernel.FormPair K)
    (∑ k : OAI.MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration.Index (d + e),
        HSMul.hSMul (α := K) (β := OAI.MatrixMultiplication.AuxiliarySeparation.DeterminantKernel.FormPair K)
          (OAI.MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration.adaptedTensor d e i j k)
          (OAI.MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration.vector (d + e) k) :
      OAI.MatrixMultiplication.AuxiliarySeparation.DeterminantKernel.FormPair K)
    ((OAI.MatrixMultiplication.AuxiliarySeparation.DeterminantKernel.multiply
          (HPow.hPow (α := Polynomial K) Polynomial.X ↑i))
        (OAI.MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration.vector e j) :
      OAI.MatrixMultiplication.AuxiliarySeparation.DeterminantKernel.FormPair K)
:= by sorry
