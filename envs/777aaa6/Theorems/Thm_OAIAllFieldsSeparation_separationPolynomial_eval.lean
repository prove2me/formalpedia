-- Prove2me | Theorems.Thm_OAIAllFieldsSeparation_separationPolynomial_eval
-- name    : OAIAllFieldsSeparation.separationPolynomial_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:16:50.763769+00:00
-- url     : https://prove2.me/theorems/3a5d98af-feea-4f6b-875f-10365d10d8e4
-- title:
--   Nonzero evaluations of the separation polynomial are restrictions
-- statement:
--   Let $K$ be a field, $M>0$, and let $B_0,\ldots,B_{M-1}$ be finite coefficient tensors. Suppose $L$ has nonzero image in $K$, satisfies $3(M-1)<L$, and $\zeta\in K$ is a primitive $L$th root of unity. For every $t\ne0$, the separation polynomial tensor $Q_{\zeta,B}$ obeys
--   \[
--   Q_{\zeta,B}(t)=\operatorname{restrict}(F_{\zeta,t},G_{\zeta,t},H_{\zeta,t})\!\left(\bigoplus_{r<L}T_B\right),
--   \]
--   where $T_B$ is the shared-first tensor and the maps are the explicit Fourier substitutions weighted by powers of $t$. This realizes every nonzero evaluation by ordinary linear restrictions.
-- source:
--   https://prove2.me/submissions/facf5b05-d302-42c1-a107-8ff40a0c2134; OAIAllFieldsSeparation.separationPolynomial_eval, lines 14844-14873

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
import Definitions.Def_OAI429_GenericFiniteProjection
import Definitions.Def_OAI429_GenericRank
import Definitions.Def_OAI429_GenericSeparation
import Theorems.Thm_OAIAllFieldsSeparation_finiteProjection_restrict
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical

theorem OAIAllFieldsSeparation.separationPolynomial_eval.{u_1, u_2, u_3, u_4} :
    ∀ {K : Type u_1} [inst : Field K] {M L : Nat} {X : Type u_2} {Y : Type u_3} {Z : Type u_4} [inst_1 : Fintype X]
  [inst_2 : Fintype Y] [inst_3 : Fintype Z] {ζ : K},
  @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) M →
    @Ne K
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
                        (@EuclideanDomain.toCommRing K (@Field.toEuclideanDomain K inst)))))))))) →
      @LT.lt Nat instLTNat
          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) M
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          L →
        @IsPrimitiveRoot K (@CommRing.toCommMonoid K (@EuclideanDomain.toCommRing K (@Field.toEuclideanDomain K inst)))
            ζ L →
          ∀ (B : Fin M → OAI.MatrixMultiplication.Foundation.Tensor K X Y Z) (t : K),
            @Ne K t
                (@OfNat.ofNat K (nat_lit 0)
                  (@Zero.toOfNat0 K
                    (@MulZeroClass.toZero K
                      (@NonUnitalNonAssocSemiring.toMulZeroClass K
                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                              (@CommRing.toNonUnitalCommRing K
                                (@EuclideanDomain.toCommRing K (@Field.toEuclideanDomain K inst)))))))))) →
              @Eq (Prod X (Fin M) → Prod (Prod (Fin M) Y) (Fin M) → Prod (Prod (Fin M) Z) (Fin M) → K)
                (fun (x : Prod X (Fin M)) (y : Prod (Prod (Fin M) Y) (Fin M)) (z : Prod (Prod (Fin M) Z) (Fin M)) =>
                  @Polynomial.eval K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))) t
                    (@OAIAllFieldsSeparation.separationPolynomial K inst M L X Y Z ζ B x y z))
                (@OAI.MatrixMultiplication.Foundation.Tensor.restrict K (Prod (Fin L) X) (Prod (Fin L) (Prod (Fin M) Y))
                  (Prod (Fin L) (Prod (Fin M) Z)) (Prod X (Fin M)) (Prod (Prod (Fin M) Y) (Fin M))
                  (Prod (Prod (Fin M) Z) (Fin M)) (@Semifield.toCommSemiring K (@Field.toSemifield K inst))
                  (@instFintypeProd (Fin L) X (Fin.fintype L) inst_1)
                  (@instFintypeProd (Fin L) (Prod (Fin M) Y) (Fin.fintype L)
                    (@instFintypeProd (Fin M) Y (Fin.fintype M) inst_2))
                  (@instFintypeProd (Fin L) (Prod (Fin M) Z) (Fin.fintype L)
                    (@instFintypeProd (Fin M) Z (Fin.fintype M) inst_3))
                  (@OAIAllFieldsSeparation.firstSeparationMap K inst M L X ζ t)
                  (@OAIAllFieldsSeparation.secondSeparationMap K inst M L Y ζ t)
                  (@OAIAllFieldsSeparation.thirdSeparationMap K inst M L Z ζ t)
                  (@OAI.MatrixMultiplication.Foundation.Tensor.directSum K X (Prod (Fin M) Y) (Prod (Fin M) Z)
                    (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) (Fin L) (instDecidableEqFin L)
                    fun (x : Fin L) => @OAIAllFieldsSeparation.sharedFirstTensor K inst M X Y Z B))
:= by sorry
