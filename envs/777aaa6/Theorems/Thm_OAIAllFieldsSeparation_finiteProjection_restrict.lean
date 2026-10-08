-- Prove2me | Theorems.Thm_OAIAllFieldsSeparation_finiteProjection_restrict
-- name    : OAIAllFieldsSeparation.finiteProjection_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:14:45.685225+00:00
-- url     : https://prove2.me/theorems/d3f456e7-2bc7-4d37-9720-da4d656ad693
-- title:
--   Finite Fourier projection is an explicit tensor restriction
-- statement:
--   Let $K$ be a field, let $M,L\in\mathbb N$, and let $B_0,\ldots,B_{M-1}$ be tensors on finite sets $X,Y,Z$. Their shared-first tensor is $T_B(x,(h,y),(k,z))=B_h(x,y,z)$ for $h=k$, and zero otherwise. For any $\zeta\in K$ with $\zeta\ne0$, the three explicit Fourier maps satisfy
--   \[
--   \operatorname{restrict}(F_\zeta,G_\zeta,H_\zeta)\!\left(\bigoplus_{r<L}T_B\right)=P_\zeta(B).
--   \]
--   Here $P_\zeta(B)$ is the defined projected tensor, whose surviving branch coefficients are multiplied by the normalized sum $L^{-1}\sum_{r<L}\zeta^{r\phi}$ for the integer phase $\phi$. This identity does not yet require a primitive root or a nonzero cast of $L$.
-- source:
--   https://prove2.me/submissions/facf5b05-d302-42c1-a107-8ff40a0c2134; OAIAllFieldsSeparation.finiteProjection_restrict, lines 14702-14750

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
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical

theorem OAIAllFieldsSeparation.finiteProjection_restrict.{u_1, u_2, u_3, u_4} :
    ∀ {K : Type u_1} [inst : Field K] {M L : ℕ} {X : Type u_2} {Y : Type u_3} {Z : Type u_4} [inst_1 : Fintype X]
  [inst_2 : Fintype Y] [inst_3 : Fintype Z] (ζ : K),
  ζ ≠ 0 →
    ∀ (B : Fin M → OAI.MatrixMultiplication.Foundation.Tensor K X Y Z),
      OAI.MatrixMultiplication.Foundation.Tensor.restrict (X := Fin L × X) (OAIAllFieldsSeparation.firstProjectionMap ζ)
          (OAIAllFieldsSeparation.secondProjectionMap ζ) (OAIAllFieldsSeparation.thirdProjectionMap ζ)
          (OAI.MatrixMultiplication.Foundation.Tensor.directSum fun (x : Fin L) =>
            OAIAllFieldsSeparation.sharedFirstTensor B) =
        OAIAllFieldsSeparation.projectedTensor (L := L) ζ B
:= by sorry
