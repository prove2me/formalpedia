-- Prove2me | Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_isClosed_pointedCone_hull_range
-- name    : OAI.MatrixMultiplication.AuxiliarySeparation.isClosed_pointedCone_hull_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:06:02.459974+00:00
-- url     : https://prove2.me/theorems/e753ba4f-fa70-4146-aea2-155ce305ba95
-- title:
--   Every finitely generated real cone is closed
-- statement:
--   Let $I$ be finite, $E$ a real normed vector space, and $A:I\to E$ any family. Then
--   \[
--   \operatorname{cone}_{\mathbb R}\{A_i:i\in I\}\text{ is closed in }E.
--   \]
--   This supplies the closedness hypothesis for the finite-dimensional separation argument without requiring the generators to be independent.
-- source:
--   https://prove2.me/submissions/facf5b05-d302-42c1-a107-8ff40a0c2134; OAI.MatrixMultiplication.AuxiliarySeparation.isClosed_pointedCone_hull_range, lines 968-989

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
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_exists_linearIndependent_subcone
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_isClosed_pointedCone_hull_range_of_linearIndependent
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical

theorem OAI.MatrixMultiplication.AuxiliarySeparation.isClosed_pointedCone_hull_range.{u_1, u_2} :
    ∀ {I : Type u_1} {E : Type u_2} [Fintype I] [inst : NormedAddCommGroup E]
  [inst_1 : @NormedSpace Real E Real.normedField (@NormedAddCommGroup.toSeminormedAddCommGroup E inst)] (A : I → E),
  @IsClosed E
    (@UniformSpace.toTopologicalSpace E
      (@PseudoMetricSpace.toUniformSpace E
        (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst))))
    (@SetLike.coe
      (@PointedCone Real E Real.semiring Real.partialOrder Real.instIsOrderedRing
        (@ESeminormedAddCommMonoid.toAddCommMonoid E
          (@UniformSpace.toTopologicalSpace E
            (@PseudoMetricSpace.toUniformSpace E
              (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst))))
          (@ENormedAddCommMonoid.toESeminormedAddCommMonoid E
            (@UniformSpace.toTopologicalSpace E
              (@PseudoMetricSpace.toUniformSpace E
                (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst))))
            (@NormedAddCommGroup.toENormedAddCommMonoid E inst)))
        (@NormedSpace.toModule Real E Real.normedField (@NormedAddCommGroup.toSeminormedAddCommGroup E inst) inst_1))
      E
      (@Submodule.setLike
        (@Subtype Real fun (c : Real) =>
          @LE.le Real (@Preorder.toLE Real (@PartialOrder.toPreorder Real Real.partialOrder))
            (@OfNat.ofNat Real (nat_lit 0)
              (@Zero.toOfNat0 Real
                (@MulZeroClass.toZero Real
                  (@NonUnitalNonAssocSemiring.toMulZeroClass Real
                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring Real
                      (@Semiring.toNonAssocSemiring Real Real.semiring))))))
            c)
        E
        (@Nonneg.semiring Real Real.semiring Real.partialOrder
          (@IsOrderedRing.toZeroLEOneClass Real Real.semiring Real.partialOrder Real.instIsOrderedRing)
          (@PointedCone._proof_1 Real Real.semiring Real.partialOrder Real.instIsOrderedRing)
          (@IsOrderedRing.toPosMulMono Real Real.semiring Real.partialOrder Real.instIsOrderedRing))
        (@ESeminormedAddCommMonoid.toAddCommMonoid E
          (@UniformSpace.toTopologicalSpace E
            (@PseudoMetricSpace.toUniformSpace E
              (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst))))
          (@ENormedAddCommMonoid.toESeminormedAddCommMonoid E
            (@UniformSpace.toTopologicalSpace E
              (@PseudoMetricSpace.toUniformSpace E
                (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst))))
            (@NormedAddCommGroup.toENormedAddCommMonoid E inst)))
        (@Nonneg.instModule Real E Real.semiring Real.partialOrder Real.instIsOrderedRing
          (@ESeminormedAddCommMonoid.toAddCommMonoid E
            (@UniformSpace.toTopologicalSpace E
              (@PseudoMetricSpace.toUniformSpace E
                (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst))))
            (@ENormedAddCommMonoid.toESeminormedAddCommMonoid E
              (@UniformSpace.toTopologicalSpace E
                (@PseudoMetricSpace.toUniformSpace E
                  (@SeminormedAddCommGroup.toPseudoMetricSpace E
                    (@NormedAddCommGroup.toSeminormedAddCommGroup E inst))))
              (@NormedAddCommGroup.toENormedAddCommMonoid E inst)))
          (@NormedSpace.toModule Real E Real.normedField (@NormedAddCommGroup.toSeminormedAddCommGroup E inst) inst_1)))
      (@PointedCone.span Real E Real.semiring Real.partialOrder Real.instIsOrderedRing
        (@ESeminormedAddCommMonoid.toAddCommMonoid E
          (@UniformSpace.toTopologicalSpace E
            (@PseudoMetricSpace.toUniformSpace E
              (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst))))
          (@ENormedAddCommMonoid.toESeminormedAddCommMonoid E
            (@UniformSpace.toTopologicalSpace E
              (@PseudoMetricSpace.toUniformSpace E
                (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst))))
            (@NormedAddCommGroup.toENormedAddCommMonoid E inst)))
        (@NormedSpace.toModule Real E Real.normedField (@NormedAddCommGroup.toSeminormedAddCommGroup E inst) inst_1)
        (@Set.range E I A)))
:= by sorry
