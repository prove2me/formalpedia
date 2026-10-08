-- Prove2me | Theorems.Thm_fixed_point_unit_cube
-- name    : fixed_point_unit_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:26:29.676329+00:00
-- url     : https://prove2.me/theorems/53efc952-8937-4297-899b-1df3e0101347
-- title:
--   Brouwer fixed points for a finite-dimensional unit cube
-- statement:
--   For every natural number $n$, let $Q=[0,1]^n$. Every continuous map $f:Q\to Q$ has a fixed point:
--
--   $$\exists x\in Q,\qquad f(x)=x.$$
--
--   The zero-dimensional cube is included. This is the cubical form of Brouwer's fixed-point theorem.
-- source:
--   https://prove2.me/submissions/facf5b05-d302-42c1-a107-8ff40a0c2134; fixed_point_unit_cube, lines 4221-4271

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
import Definitions.Def_OAI429_FixedPointTheorems_apply_cubical_sperner
import Definitions.Def_OAI429_FixedPointTheorems_cubical_sperner_prep
import Theorems.Thm_monotone_1_of_simplex
import Theorems.Thm_strong_cubical_sperner
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical

theorem fixed_point_unit_cube :
    ∀ {n : Nat}
  (f :
    @ContinuousMap (@Set.Elem (Fin n → Real) (@unit_cube n)) (@Set.Elem (Fin n → Real) (@unit_cube n))
      (@instTopologicalSpaceSubtype (Fin n → Real)
        (fun (x : Fin n → Real) =>
          @Membership.mem (Fin n → Real) (Set (Fin n → Real)) (@Set.instMembership (Fin n → Real)) (@unit_cube n) x)
        (@Pi.topologicalSpace (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
          @UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
      (@instTopologicalSpaceSubtype (Fin n → Real)
        (fun (x : Fin n → Real) =>
          @Membership.mem (Fin n → Real) (Set (Fin n → Real)) (@Set.instMembership (Fin n → Real)) (@unit_cube n) x)
        (@Pi.topologicalSpace (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
          @UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))),
  ∃ (x : @Set.Elem (Fin n → Real) (@unit_cube n)),
    @Eq (@Set.Elem (Fin n → Real) (@unit_cube n))
      (@DFunLike.coe
        (@ContinuousMap (@Set.Elem (Fin n → Real) (@unit_cube n)) (@Set.Elem (Fin n → Real) (@unit_cube n))
          (@instTopologicalSpaceSubtype (Fin n → Real)
            (fun (x : Fin n → Real) =>
              @Membership.mem (Fin n → Real) (Set (Fin n → Real)) (@Set.instMembership (Fin n → Real)) (@unit_cube n) x)
            (@Pi.topologicalSpace (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
              @UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
          (@instTopologicalSpaceSubtype (Fin n → Real)
            (fun (x : Fin n → Real) =>
              @Membership.mem (Fin n → Real) (Set (Fin n → Real)) (@Set.instMembership (Fin n → Real)) (@unit_cube n) x)
            (@Pi.topologicalSpace (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
              @UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))))
        (@Set.Elem (Fin n → Real) (@unit_cube n))
        (fun (x : @Set.Elem (Fin n → Real) (@unit_cube n)) => @Set.Elem (Fin n → Real) (@unit_cube n))
        (@ContinuousMap.instFunLike (@Set.Elem (Fin n → Real) (@unit_cube n)) (@Set.Elem (Fin n → Real) (@unit_cube n))
          (@instTopologicalSpaceSubtype (Fin n → Real)
            (fun (x : Fin n → Real) =>
              @Membership.mem (Fin n → Real) (Set (Fin n → Real)) (@Set.instMembership (Fin n → Real)) (@unit_cube n) x)
            (@Pi.topologicalSpace (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
              @UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
          (@instTopologicalSpaceSubtype (Fin n → Real)
            (fun (x : Fin n → Real) =>
              @Membership.mem (Fin n → Real) (Set (Fin n → Real)) (@Set.instMembership (Fin n → Real)) (@unit_cube n) x)
            (@Pi.topologicalSpace (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
              @UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))))
        f x)
      x
:= by sorry
