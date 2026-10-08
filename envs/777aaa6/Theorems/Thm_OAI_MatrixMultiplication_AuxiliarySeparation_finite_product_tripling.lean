-- Prove2me | Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_finite_product_tripling
-- name    : OAI.MatrixMultiplication.AuxiliarySeparation.finite_product_tripling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:12:12.345928+00:00
-- url     : https://prove2.me/theorems/eafeca42-11a3-4bc5-97b7-3d2a4051ce73
-- title:
--   Cyclic tensor bounds imply tripling of normalized products
-- statement:
--   Let $I$ be finite, let $A_i,B_i,C_i>0$, and let $p_i\in\mathbb R$ satisfy $s=\sum_i p_i>0$. Suppose
--   \[
--   3^{p_i}B_i^{2/3}C_i^{1/3}\le A_i\quad(i\in I),
--   \qquad\prod_i C_i=\prod_i B_i.
--   \]
--   Then
--   \[
--   3\left(\prod_i B_i\right)^{1/s}\le\left(\prod_i A_i\right)^{1/s}.
--   \]
--   This yields the factor three in the scalar profile’s shifted tripling inequality.
-- source:
--   https://prove2.me/submissions/facf5b05-d302-42c1-a107-8ff40a0c2134; OAI.MatrixMultiplication.AuxiliarySeparation.finite_product_tripling, lines 10750-10778

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

theorem OAI.MatrixMultiplication.AuxiliarySeparation.finite_product_tripling.{u_1} :
    ∀ {ι : Type u_1} [inst : Fintype ι] (A B C p : ι → Real) {s : Real},
  @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) s →
    @Eq Real (∑ i : ι, p i) s →
      (∀ (i : ι), @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) (A i)) →
        (∀ (i : ι), @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) (B i)) →
          (∀ (i : ι),
              @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) (C i)) →
            (∀ (i : ι),
                @LE.le Real Real.instLE
                  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                      (@HPow.hPow Real Real Real (@instHPow Real Real Real.instPow)
                        (@OfNat.ofNat Real (nat_lit 3)
                          (@instOfNatAtLeastTwo Real (nat_lit 3) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                        (p i))
                      (@HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (B i)
                        (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                          (@OfNat.ofNat Real (nat_lit 2)
                            (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          (@OfNat.ofNat Real (nat_lit 3)
                            (@instOfNatAtLeastTwo Real (nat_lit 3) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))
                    (@HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (C i)
                      (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                        (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                        (@OfNat.ofNat Real (nat_lit 3)
                          (@instOfNatAtLeastTwo Real (nat_lit 3) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))
                  (A i)) →
              @Eq Real (∏ i : ι, C i) (∏ i : ι, B i) →
                @LE.le Real Real.instLE
                  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                    (@OfNat.ofNat Real (nat_lit 3)
                      (@instOfNatAtLeastTwo Real (nat_lit 3) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                    (@HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (∏ i : ι, B i)
                      (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                        (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) s)))
                  (@HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (∏ i : ι, A i)
                    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                      (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) s))
:= by sorry
