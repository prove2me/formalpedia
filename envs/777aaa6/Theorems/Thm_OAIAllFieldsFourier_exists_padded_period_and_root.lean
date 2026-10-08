-- Prove2me | Theorems.Thm_OAIAllFieldsFourier_exists_padded_period_and_root
-- name    : OAIAllFieldsFourier.exists_padded_period_and_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:14:19.738151+00:00
-- url     : https://prove2.me/theorems/f48d093a-3578-4284-bc09-021224d99551
-- title:
--   A characteristic-safe Fourier period preserves the constant five
-- statement:
--   Let $K$ be any algebraically closed field and let $M>0$ be a natural number. There exist a natural number $L$ and $\zeta\in K$ such that
--   \[
--   L\in\{5M,5M-1\},\qquad L\cdot1_K\ne0,\qquad 3(M-1)<L\le5M,
--   \]
--   and $\zeta$ is a primitive $L$th root of unity. Thus normalized Fourier averaging can be performed in every characteristic while retaining the original five-$M$ upper bound.
-- source:
--   https://prove2.me/submissions/facf5b05-d302-42c1-a107-8ff40a0c2134; OAIAllFieldsFourier.exists_padded_period_and_root, lines 14297-14305

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

theorem OAIAllFieldsFourier.exists_padded_period_and_root.{u_2} :
    ∀ (K : Type u_2) [inst : Field K] [@IsAlgClosed K inst] (M : Nat),
  @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) M →
    ∃ (L : Nat) (ζ : K),
      And
        (Or
          (@Eq Nat L
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
              M))
          (@Eq Nat L
            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) M)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (And
          (@Ne K
            (@Nat.cast K
              (@AddMonoidWithOne.toNatCast K
                (@AddGroupWithOne.toAddMonoidWithOne K
                  (@Ring.toAddGroupWithOne K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))))
              L)
            (@OfNat.ofNat K (nat_lit 0)
              (@Zero.toOfNat0 K
                (@MulZeroClass.toZero K
                  (@NonUnitalNonAssocSemiring.toMulZeroClass K
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                          (@CommRing.toNonUnitalCommRing K
                            (@EuclideanDomain.toCommRing K (@Field.toEuclideanDomain K inst)))))))))))
          (And
            (@LT.lt Nat instLTNat
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) M
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              L)
            (And
              (@LE.le Nat instLENat L
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                  (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) M))
              (@IsPrimitiveRoot K
                (@CommRing.toCommMonoid K (@EuclideanDomain.toCommRing K (@Field.toEuclideanDomain K inst))) ζ L))))
:= by sorry
