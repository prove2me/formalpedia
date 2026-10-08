-- Prove2me | Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_exists_approximate_fixedPoint_of_weights
-- name    : OAI.MatrixMultiplication.AuxiliarySeparation.exists_approximate_fixedPoint_of_weights
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:28:46.333572+00:00
-- url     : https://prove2.me/theorems/9bfb753c-b32e-4506-bf9b-aa76ad6cb0f9
-- title:
--   Barycentric weights yield an approximate fixed point
-- statement:
--   Let $I$ be any index set, $K\subseteq\mathbb R^I$ convex, and $f:K\to K$ continuous. Let $J$ be finite and nonempty, with points $a_j\in K$ and continuous weights $w_j:K\to\mathbb R$ satisfying $w_j(x)\ge0$ and $\sum_jw_j(x)=1$. Let $F\subseteq I$ be finite and $\varepsilon\in\mathbb R$. Assume $w_j(x)\ne0$ implies $|a_j(i)-x(i)|\le\varepsilon$ for every $i\in F$. Then
--
--   $$\exists x\in K\;\forall i\in F,\quad |f(x)(i)-x(i)|\le\varepsilon.$$
--
--   Only the prescribed finite coordinates are controlled; the ambient product need not be finite-dimensional.
-- source:
--   https://prove2.me/submissions/facf5b05-d302-42c1-a107-8ff40a0c2134; OAI.MatrixMultiplication.AuxiliarySeparation.exists_approximate_fixedPoint_of_weights, lines 4504-4559

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
import Definitions.Def_OAI429_OAI_LinearAlgebra_MatrixMultiplication_AuxiliarySeparation_Convex_FixedPoint
import Theorems.Thm_fixed_point_unit_cube
import Theorems.Thm_homeo_unit_cube_of_convex_compact
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical

theorem OAI.MatrixMultiplication.AuxiliarySeparation.exists_approximate_fixedPoint_of_weights.{u_1, u_2} :
    ∀ {I : Type u_1} {J : Type u_2} [inst : Fintype J] [Nonempty J] {K : Set (I → Real)},
  @Convex Real (I → Real) Real.semiring Real.partialOrder
      (@Pi.addCommMonoid I (fun (a : I) => Real) fun (i : I) => Real.instAddCommMonoid)
      (@Function.hasSMul I Real Real
        (@Algebra.toSMul Real Real Real.instCommSemiring (@CommSemiring.toSemiring Real Real.instCommSemiring)
          (@Algebra.id Real Real.instCommSemiring)))
      K →
    ∀
      (f :
        @ContinuousMap (@Set.Elem (I → Real) K) (@Set.Elem (I → Real) K)
          (@instTopologicalSpaceSubtype (I → Real)
            (fun (x : I → Real) => @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
            (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
              @UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
          (@instTopologicalSpaceSubtype (I → Real)
            (fun (x : I → Real) => @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
            (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
              @UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))))
      (a : J → @Set.Elem (I → Real) K)
      (w :
        J →
          @ContinuousMap (@Set.Elem (I → Real) K) Real
            (@instTopologicalSpaceSubtype (I → Real)
              (fun (x : I → Real) => @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
              (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                @UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
            (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))),
      (∀ (j : J) (x : @Set.Elem (I → Real) K),
          @LE.le Real Real.instLE (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
            (@DFunLike.coe
              (@ContinuousMap (@Set.Elem (I → Real) K) Real
                (@instTopologicalSpaceSubtype (I → Real)
                  (fun (x : I → Real) =>
                    @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                  (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                    @UniformSpace.toTopologicalSpace Real
                      (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
              (@Set.Elem (I → Real) K) (fun (x : @Set.Elem (I → Real) K) => Real)
              (@ContinuousMap.instFunLike (@Set.Elem (I → Real) K) Real
                (@instTopologicalSpaceSubtype (I → Real)
                  (fun (x : I → Real) =>
                    @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                  (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                    @UniformSpace.toTopologicalSpace Real
                      (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
              (w j) x)) →
        (∀ (x : @Set.Elem (I → Real) K),
            @Eq Real
              (∑ j : J,
                @DFunLike.coe
                  (@ContinuousMap (@Set.Elem (I → Real) K) Real
                    (@instTopologicalSpaceSubtype (I → Real)
                      (fun (x : I → Real) =>
                        @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                      (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                        @UniformSpace.toTopologicalSpace Real
                          (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                    (@UniformSpace.toTopologicalSpace Real
                      (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                  (@Set.Elem (I → Real) K) (fun (x : @Set.Elem (I → Real) K) => Real)
                  (@ContinuousMap.instFunLike (@Set.Elem (I → Real) K) Real
                    (@instTopologicalSpaceSubtype (I → Real)
                      (fun (x : I → Real) =>
                        @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                      (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                        @UniformSpace.toTopologicalSpace Real
                          (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                    (@UniformSpace.toTopologicalSpace Real
                      (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                  (w j) x)
              (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))) →
          ∀ (s : Finset I) (ε : Real),
            (∀ (x : @Set.Elem (I → Real) K) (j : J),
                @Ne Real
                    (@DFunLike.coe
                      (@ContinuousMap (@Set.Elem (I → Real) K) Real
                        (@instTopologicalSpaceSubtype (I → Real)
                          (fun (x : I → Real) =>
                            @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                          (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                            @UniformSpace.toTopologicalSpace Real
                              (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                        (@UniformSpace.toTopologicalSpace Real
                          (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                      (@Set.Elem (I → Real) K) (fun (x : @Set.Elem (I → Real) K) => Real)
                      (@ContinuousMap.instFunLike (@Set.Elem (I → Real) K) Real
                        (@instTopologicalSpaceSubtype (I → Real)
                          (fun (x : I → Real) =>
                            @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                          (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                            @UniformSpace.toTopologicalSpace Real
                              (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                        (@UniformSpace.toTopologicalSpace Real
                          (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                      (w j) x)
                    (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) →
                  ∀ (i : I),
                    @Membership.mem I (Finset I) (@SetLike.instMembership (Finset I) I (@Finset.instSetLike I)) s i →
                      @LE.le Real Real.instLE
                        (@abs Real Real.lattice Real.instAddGroup
                          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                            (@Subtype.val (I → Real)
                              (fun (x : I → Real) =>
                                @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                              (a j) i)
                            (@Subtype.val (I → Real)
                              (fun (x : I → Real) =>
                                @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                              x i)))
                        ε) →
              ∃ (x : @Set.Elem (I → Real) K),
                ∀ (i : I),
                  @Membership.mem I (Finset I) (@SetLike.instMembership (Finset I) I (@Finset.instSetLike I)) s i →
                    @LE.le Real Real.instLE
                      (@abs Real Real.lattice Real.instAddGroup
                        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                          (@Subtype.val (I → Real)
                            (fun (x : I → Real) =>
                              @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                            (@DFunLike.coe
                              (@ContinuousMap (@Set.Elem (I → Real) K) (@Set.Elem (I → Real) K)
                                (@instTopologicalSpaceSubtype (I → Real)
                                  (fun (x : I → Real) =>
                                    @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                                  (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                                    @UniformSpace.toTopologicalSpace Real
                                      (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                                (@instTopologicalSpaceSubtype (I → Real)
                                  (fun (x : I → Real) =>
                                    @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                                  (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                                    @UniformSpace.toTopologicalSpace Real
                                      (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))))
                              (@Set.Elem (I → Real) K) (fun (x : @Set.Elem (I → Real) K) => @Set.Elem (I → Real) K)
                              (@ContinuousMap.instFunLike (@Set.Elem (I → Real) K) (@Set.Elem (I → Real) K)
                                (@instTopologicalSpaceSubtype (I → Real)
                                  (fun (x : I → Real) =>
                                    @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                                  (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                                    @UniformSpace.toTopologicalSpace Real
                                      (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                                (@instTopologicalSpaceSubtype (I → Real)
                                  (fun (x : I → Real) =>
                                    @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                                  (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                                    @UniformSpace.toTopologicalSpace Real
                                      (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))))
                              f x)
                            i)
                          (@Subtype.val (I → Real)
                            (fun (x : I → Real) =>
                              @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                            x i)))
                      ε
:= by sorry
