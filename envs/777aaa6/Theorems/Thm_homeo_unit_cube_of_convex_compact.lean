-- Prove2me | Theorems.Thm_homeo_unit_cube_of_convex_compact
-- name    : homeo_unit_cube_of_convex_compact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:06:08.840382+00:00
-- url     : https://prove2.me/theorems/9c9e27db-e05b-4e2e-ae79-d5eac6329bac
-- title:
--   A nonempty compact convex set is homeomorphic to a cube of its affine dimension
-- statement:
--   Let $V$ be a finite-dimensional real normed vector space and let $S\subseteq V$ be nonempty, compact, and convex. There is a natural number $k$ for which
--
--   $$S\cong[0,1]^k$$
--
--   as topological spaces. The dimension may be zero, which includes singleton sets. This permits fixed-point results for cubes to be transferred to arbitrary compact convex sets.
-- source:
--   https://prove2.me/submissions/facf5b05-d302-42c1-a107-8ff40a0c2134; homeo_unit_cube_of_convex_compact, lines 4350-4410

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
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical

theorem homeo_unit_cube_of_convex_compact.{u_1} :
    ∀ {V : Type u_1} [inst : NormedAddCommGroup V]
  [inst_1 : @NormedSpace Real V Real.normedField (@NormedAddCommGroup.toSeminormedAddCommGroup V inst)]
  [@FiniteDimensional Real V Real.instDivisionRing (@NormedAddCommGroup.toAddCommGroup V inst)
      (@NormedSpace.toModule Real V Real.normedField (@NormedAddCommGroup.toSeminormedAddCommGroup V inst) inst_1)]
  (s : Set V),
  @Convex Real V Real.semiring Real.partialOrder
      (@ESeminormedAddCommMonoid.toAddCommMonoid V
        (@UniformSpace.toTopologicalSpace V
          (@PseudoMetricSpace.toUniformSpace V
            (@SeminormedAddCommGroup.toPseudoMetricSpace V (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
        (@ENormedAddCommMonoid.toESeminormedAddCommMonoid V
          (@UniformSpace.toTopologicalSpace V
            (@PseudoMetricSpace.toUniformSpace V
              (@SeminormedAddCommGroup.toPseudoMetricSpace V (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
          (@NormedAddCommGroup.toENormedAddCommMonoid V inst)))
      (@SMulZeroClass.toSMul Real V
        (@AddZero.toZero V
          (@AddZeroClass.toAddZero V
            (@AddMonoid.toAddZeroClass V
              (@ESeminormedAddMonoid.toAddMonoid V
                (@UniformSpace.toTopologicalSpace V
                  (@PseudoMetricSpace.toUniformSpace V
                    (@SeminormedAddCommGroup.toPseudoMetricSpace V
                      (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
                (@ESeminormedAddCommMonoid.toESeminormedAddMonoid V
                  (@UniformSpace.toTopologicalSpace V
                    (@PseudoMetricSpace.toUniformSpace V
                      (@SeminormedAddCommGroup.toPseudoMetricSpace V
                        (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
                  (@ENormedAddCommMonoid.toESeminormedAddCommMonoid V
                    (@UniformSpace.toTopologicalSpace V
                      (@PseudoMetricSpace.toUniformSpace V
                        (@SeminormedAddCommGroup.toPseudoMetricSpace V
                          (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
                    (@NormedAddCommGroup.toENormedAddCommMonoid V inst)))))))
        (@DistribSMul.toSMulZeroClass Real V
          (@AddMonoid.toAddZeroClass V
            (@ESeminormedAddMonoid.toAddMonoid V
              (@UniformSpace.toTopologicalSpace V
                (@PseudoMetricSpace.toUniformSpace V
                  (@SeminormedAddCommGroup.toPseudoMetricSpace V
                    (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
              (@ESeminormedAddCommMonoid.toESeminormedAddMonoid V
                (@UniformSpace.toTopologicalSpace V
                  (@PseudoMetricSpace.toUniformSpace V
                    (@SeminormedAddCommGroup.toPseudoMetricSpace V
                      (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
                (@ENormedAddCommMonoid.toESeminormedAddCommMonoid V
                  (@UniformSpace.toTopologicalSpace V
                    (@PseudoMetricSpace.toUniformSpace V
                      (@SeminormedAddCommGroup.toPseudoMetricSpace V
                        (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
                  (@NormedAddCommGroup.toENormedAddCommMonoid V inst)))))
          (@DistribMulAction.toDistribSMul Real V Real.instMonoid
            (@ESeminormedAddMonoid.toAddMonoid V
              (@UniformSpace.toTopologicalSpace V
                (@PseudoMetricSpace.toUniformSpace V
                  (@SeminormedAddCommGroup.toPseudoMetricSpace V
                    (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
              (@ESeminormedAddCommMonoid.toESeminormedAddMonoid V
                (@UniformSpace.toTopologicalSpace V
                  (@PseudoMetricSpace.toUniformSpace V
                    (@SeminormedAddCommGroup.toPseudoMetricSpace V
                      (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
                (@ENormedAddCommMonoid.toESeminormedAddCommMonoid V
                  (@UniformSpace.toTopologicalSpace V
                    (@PseudoMetricSpace.toUniformSpace V
                      (@SeminormedAddCommGroup.toPseudoMetricSpace V
                        (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
                  (@NormedAddCommGroup.toENormedAddCommMonoid V inst))))
            (@Module.toDistribMulAction Real V Real.semiring
              (@ESeminormedAddCommMonoid.toAddCommMonoid V
                (@UniformSpace.toTopologicalSpace V
                  (@PseudoMetricSpace.toUniformSpace V
                    (@SeminormedAddCommGroup.toPseudoMetricSpace V
                      (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
                (@ENormedAddCommMonoid.toESeminormedAddCommMonoid V
                  (@UniformSpace.toTopologicalSpace V
                    (@PseudoMetricSpace.toUniformSpace V
                      (@SeminormedAddCommGroup.toPseudoMetricSpace V
                        (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
                  (@NormedAddCommGroup.toENormedAddCommMonoid V inst)))
              (@NormedSpace.toModule Real V Real.normedField (@NormedAddCommGroup.toSeminormedAddCommGroup V inst)
                inst_1)))))
      s →
    @IsCompact V
        (@UniformSpace.toTopologicalSpace V
          (@PseudoMetricSpace.toUniformSpace V
            (@SeminormedAddCommGroup.toPseudoMetricSpace V (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
        s →
      @Set.Nonempty V s →
        ∃ (k : Nat),
          Nonempty.{max 1 (u_1 + 1)}
            (@Homeomorph (@Set.Elem V s)
              (@Set.Elem (Fin k → Real)
                (@Set.Icc (Fin k → Real)
                  (@Pi.preorder (Fin k) (fun (a : Fin k) => Real) fun (i : Fin k) => Real.instPreorder)
                  (@OfNat.ofNat (Fin k → Real) (nat_lit 0)
                    (@Zero.toOfNat0 (Fin k → Real)
                      (@Pi.instZero (Fin k) (fun (a : Fin k) => Real) fun (i : Fin k) => Real.instZero)))
                  (@OfNat.ofNat (Fin k → Real) (nat_lit 1)
                    (@One.toOfNat1 (Fin k → Real)
                      (@Pi.instOne (Fin k) (fun (a : Fin k) => Real) fun (i : Fin k) => Real.instOne)))))
              (@instTopologicalSpaceSubtype V (fun (x : V) => @Membership.mem V (Set V) (@Set.instMembership V) s x)
                (@UniformSpace.toTopologicalSpace V
                  (@PseudoMetricSpace.toUniformSpace V
                    (@SeminormedAddCommGroup.toPseudoMetricSpace V
                      (@NormedAddCommGroup.toSeminormedAddCommGroup V inst)))))
              (@instTopologicalSpaceSubtype (Fin k → Real)
                (fun (x : Fin k → Real) =>
                  @Membership.mem (Fin k → Real) (Set (Fin k → Real)) (@Set.instMembership (Fin k → Real))
                    (@Set.Icc (Fin k → Real)
                      (@Pi.preorder (Fin k) (fun (a : Fin k) => Real) fun (i : Fin k) => Real.instPreorder)
                      (@OfNat.ofNat (Fin k → Real) (nat_lit 0)
                        (@Zero.toOfNat0 (Fin k → Real)
                          (@Pi.instZero (Fin k) (fun (a : Fin k) => Real) fun (i : Fin k) => Real.instZero)))
                      (@OfNat.ofNat (Fin k → Real) (nat_lit 1)
                        (@One.toOfNat1 (Fin k → Real)
                          (@Pi.instOne (Fin k) (fun (a : Fin k) => Real) fun (i : Fin k) => Real.instOne))))
                    x)
                (@Pi.topologicalSpace (Fin k) (fun (a : Fin k) => Real) fun (i : Fin k) =>
                  @UniformSpace.toTopologicalSpace Real
                    (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))))
:= by sorry
