-- Prove2me | Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_Sector_convolution_tripling_tag
-- name    : OAI.MatrixMultiplication.AuxiliarySeparation.Sector.convolution_tripling_tag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:38:41.3532+00:00
-- url     : https://prove2.me/theorems/217d0f8d-3f81-43b1-b073-b400850d16c3
-- title:
--   Three-sector degeneration gives the convolution tripling tag
-- statement:
--   Let $K$ be an algebraically closed field, $\chi$ a tensor character, and $a,h>0$. Let $C^{\mathrm{ex}}(a,h)$ be polynomial convolution with its last two legs exchanged. Then
--   \[
--   3^{p_X(\chi)}\,\chi(C(a,h))^{2/3}\,\chi(C^{\mathrm{ex}}(a,h))^{1/3}
--    \le\chi(C(a,3h+a-1)).
--   \]
--   This is the three-sector inequality for one character, before symmetrization over tensor-leg permutations.
-- source:
--   https://prove2.me/submissions/facf5b05-d302-42c1-a107-8ff40a0c2134; OAI.MatrixMultiplication.AuxiliarySeparation.Sector.convolution_tripling_tag, lines 16781-16797

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
import Definitions.Def_OAI429_GenericCharacterCore
import Definitions.Def_OAI429_GenericCharacterLaws
import Definitions.Def_OAI429_GenericConvolution
import Definitions.Def_OAI429_GenericNumerics
import Definitions.Def_OAI429_GenericRank
import Definitions.Def_OAI429_GenericSectorAlgebra
import Definitions.Def_OAI429_GenericSectorBranches
import Definitions.Def_OAI429_GenericSectorCharacter
import Definitions.Def_OAI429_GenericSeparation
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical
namespace OAIAllFieldsSeparation
end OAIAllFieldsSeparation

theorem OAI.MatrixMultiplication.AuxiliarySeparation.Sector.convolution_tripling_tag.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] [@IsAlgClosed K inst]
  (χ : @OAI.MatrixMultiplication.AuxiliarySeparation.Character K inst) (a h : Nat),
  @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) a →
    @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) h →
      @LE.le Real Real.instLE
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
            (@HPow.hPow Real Real Real (@instHPow Real Real Real.instPow)
              (@OfNat.ofNat Real (nat_lit 3)
                (@instOfNatAtLeastTwo Real (nat_lit 3) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
              (@OAI.MatrixMultiplication.AuxiliarySeparation.Character.pX K inst χ))
            (@HPow.hPow Real Real Real (@instHPow Real Real Real.instPow)
              (@OAI.MatrixMultiplication.AuxiliarySeparation.Character.value K inst χ (Fin a) (Fin h)
                (Fin
                  (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a h)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (Fin.fintype a) (Fin.fintype h)
                (Fin.fintype
                  (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a h)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@OAI.MatrixMultiplication.AuxiliarySeparation.convolution K inst a h))
              (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                (@OfNat.ofNat Real (nat_lit 2)
                  (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (@OfNat.ofNat Real (nat_lit 3)
                  (@instOfNatAtLeastTwo Real (nat_lit 3) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))
          (@HPow.hPow Real Real Real (@instHPow Real Real Real.instPow)
            (@OAI.MatrixMultiplication.AuxiliarySeparation.Character.value K inst χ (Fin a)
              (Fin
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a h)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Fin h) (Fin.fintype a)
              (Fin.fintype
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a h)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Fin.fintype h)
              fun (i : Fin a)
                (s :
                  Fin
                    (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a h)
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (r : Fin h) =>
              @OAI.MatrixMultiplication.AuxiliarySeparation.convolution K inst a h i r s)
            (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
              (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
              (@OfNat.ofNat Real (nat_lit 3)
                (@instOfNatAtLeastTwo Real (nat_lit 3) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))
        (@OAI.MatrixMultiplication.AuxiliarySeparation.Character.value K inst χ (Fin a)
          (Fin
            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                  (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) h)
                a)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Fin
            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) h)
                    a)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Fin.fintype a)
          (Fin.fintype
            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                  (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) h)
                a)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Fin.fintype
            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) h)
                    a)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@OAI.MatrixMultiplication.AuxiliarySeparation.convolution K inst a
            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                  (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) h)
                a)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
:= by sorry
