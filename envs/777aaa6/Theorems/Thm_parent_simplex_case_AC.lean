-- Prove2me | Theorems.Thm_parent_simplex_case_AC
-- name    : parent_simplex_case_AC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:11:52.365313+00:00
-- url     : https://prove2.me/theorems/00993b59-2605-4879-8561-46c81587ae31
-- title:
--   Adding an upper endpoint produces a parent simplex
-- statement:
--   Let $SC$ have dimension $N=n_1+1$. Let $I$ be an $n_1$-simplex, let $j=N$, and let $J$ become $I$ after deleting position $j$. Suppose $J(j)\ne I(n_1)$ and, in every coordinate $k$,
--   \[
--   I(n_1)_k\le J(j)_k,\qquad J(j)_k\le I(0)_k+1.
--   \]
--   Coordinate values in the second inequality are natural numbers. Then $I$ is a face of the $N$-simplex $J$. This validates the parent construction obtained by inserting an upper endpoint.
-- source:
--   https://prove2.me/submissions/facf5b05-d302-42c1-a107-8ff40a0c2134; parent_simplex_case_AC, lines 2138-2211

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
import Theorems.Thm_child_simplex_char
import Theorems.Thm_monotone_1_of_simplex
import Theorems.Thm_parent_injective
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical

theorem parent_simplex_case_AC :
    ∀ (SC : SpernerCube) {n1 : Nat}
  {hn1 :
    @Eq Nat
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      SC.n}
  (I :
    Fin
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      SC.G),
  simplex SC n1 I →
    ∀
      (J :
        Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.n
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          SC.G)
      (j :
        Fin
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.n
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @Eq
          (Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.n
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          j (Fin.last SC.n) →
        @Eq
            (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
              SC.G)
            I (@delete_vertex SC n1 hn1 j J) →
          @Ne SC.G (J j) (I (Fin.last n1)) →
            (∀ (k : Fin SC.n),
                And
                  (@LE.le
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.p
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@instLEFin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.p
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (I (Fin.last n1) k) (J j k))
                  (@LE.le Nat instLENat
                    (@Fin.val
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.p
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (J j k))
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@Fin.val
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.p
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (I
                          (@OfNat.ofNat
                            (Fin
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            (nat_lit 0)
                            (@Fin.instOfNat
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (@instNeZeroNatHAdd_1 n1 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                              (nat_lit 0)))
                          k))
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
              @is_face SC n1 I J
:= by sorry
