-- Prove2me | Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_Sector_middleTensor_support
-- name    : OAI.MatrixMultiplication.AuxiliarySeparation.Sector.middleTensor_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:15:26.566368+00:00
-- url     : https://prove2.me/theorems/f9ae2a08-c437-4242-8ebc-4e23b9f6bf08
-- title:
--   Every middle-sector coefficient lies in the exchanged embeddings
-- statement:
--   Let $K$ be an algebraically closed field and $a,h\in\mathbb N$. If the middle-sector tensor has a nonzero coefficient $M_{a,h}(i,j,k)$, then there are indices $u<a$, $s<a+h-1$, and $r<h$ such that
--   \[
--   i=\operatorname{rev}(u),\qquad j=\iota_Y(s),\qquad k=\iota_Z(r),
--   \]
--   for the defined middle-sector embeddings. Thus the ambient middle tensor has no support outside the coordinates used by its exchanged-convolution identification.
-- source:
--   https://prove2.me/submissions/facf5b05-d302-42c1-a107-8ff40a0c2134; OAI.MatrixMultiplication.AuxiliarySeparation.Sector.middleTensor_support, lines 16532-16547

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
import Definitions.Def_OAI429_GenericSectorAlgebra
import Definitions.Def_OAI429_GenericSectorBranches
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical

theorem OAI.MatrixMultiplication.AuxiliarySeparation.Sector.middleTensor_support.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] [@IsAlgClosed K inst] (a h : Nat) (i : Fin a)
  (j : OAI.MatrixMultiplication.AuxiliarySeparation.Sector.YIndex a h)
  (k : OAI.MatrixMultiplication.AuxiliarySeparation.Sector.ZIndex a h),
  @Ne K (@OAI.MatrixMultiplication.AuxiliarySeparation.Sector.middleTensor K inst a h i j k)
      (@OfNat.ofNat K (nat_lit 0)
        (@Zero.toOfNat0 K
          (@MulZeroClass.toZero K
            (@NonUnitalNonAssocSemiring.toMulZeroClass K
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                    (@CommRing.toNonUnitalCommRing K
                      (@EuclideanDomain.toCommRing K (@Field.toEuclideanDomain K inst)))))))))) →
    And (∃ (u : Fin a), @Eq (Fin a) (@Fin.rev a u) i)
      (And
        (∃ (s :
          Fin
            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a h)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
          @Eq (OAI.MatrixMultiplication.AuxiliarySeparation.Sector.YIndex a h)
            (OAI.MatrixMultiplication.AuxiliarySeparation.Sector.middleY a h s) j)
        (∃ (r : Fin h),
          @Eq (OAI.MatrixMultiplication.AuxiliarySeparation.Sector.ZIndex a h)
            (OAI.MatrixMultiplication.AuxiliarySeparation.Sector.middleZ a h r) k))
:= by sorry
