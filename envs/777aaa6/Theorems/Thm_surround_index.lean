-- Prove2me | Theorems.Thm_surround_index
-- name    : surround_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:04:49.403046+00:00
-- url     : https://prove2.me/theorems/8c3eb91f-8dd8-4f9d-83c3-8f458cb9eaa6
-- title:
--   The retained indices adjacent to an omitted position
-- statement:
--   Let $SC$ be a Sperner cube of dimension $N=n_1+1$. For $j\in\{0,\ldots,N\}$, define the skipped-index map $\iota_j:\{0,\ldots,N-1\}\to\{0,\ldots,N\}$ by $\iota_j(a)=a$ when $a<j$ and $\iota_j(a)=a+1$ otherwise. Suppose $i+1=j$ as natural-number indices and $j\ne N$. Then
--   \[
--   \iota_j(i)+1=j,\qquad j+1=\iota_j(i+1).
--   \]
--   The index $i+1$ on the right is a valid successor in the smaller chain because $j$ is not the last index. These equalities locate the two retained positions immediately surrounding an inserted vertex.
-- source:
--   https://prove2.me/submissions/facf5b05-d302-42c1-a107-8ff40a0c2134; surround_index, lines 2026-2044

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
import Definitions.Def_OAI429_FixedPointTheorems_cubical_sperner_prep
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical

theorem surround_index :
    ∀ (SC : SpernerCube) {n1 : Nat}
  {hn1 :
    @Eq Nat
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      SC.n}
  (j :
    Fin
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.n
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (i :
    Fin
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
  @Eq Nat
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@Fin.val
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          i)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@Fin.val
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.n
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        j) →
    @Ne
        (Fin
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.n
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        j (Fin.last SC.n) →
      And
        (@Eq Nat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@Fin.val
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@insert_index SC n1 hn1 j i))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Fin.val
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.n
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            j))
        (@Eq Nat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@Fin.val
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              j)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Fin.val
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.n
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@insert_index SC n1 hn1 j
              (@HAdd.hAdd
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@instHAdd
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@Fin.instAdd
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                i
                (@OfNat.ofNat
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (nat_lit 1)
                  (@Fin.instOfNat
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@instNeZeroNatHAdd_1 n1 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                    (nat_lit 1)))))))
:= by sorry
