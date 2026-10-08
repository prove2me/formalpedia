-- Prove2me | Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_exactType_power_pullback
-- name    : OAI.MatrixMultiplication.AuxiliarySeparation.exactType_power_pullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:15:27.170219+00:00
-- url     : https://prove2.me/theorems/3fe7d0ae-d3d2-48a8-a8c7-c2f4d7f2812a
-- title:
--   Exact-type words restrict a tensor power to a shared family of word tensors
-- statement:
--   Let $K$ be an algebraically closed field and let $B_a$ be tensors on coordinate sets $X,Y,Z$, indexed by $a<s$. Choose counts $c_a\in\mathbb N$, put $N=\sum_a c_a$, and let $W_c$ be the words of length $N$ in which letter $a$ occurs exactly $c_a$ times. For any enumeration $e:\operatorname{Fin}|W_c|\simeq W_c$,
--   \[
--   \operatorname{pullback}(\mathrm{id},\iota_{c,e},\iota_{c,e})(T_B^{\otimes N})
--    =T_{(T_{e(h)})_{h<|W_c|}},
--   \]
--   where $\iota_{c,e}$ attaches the selected word's branch labels to each coordinate, and $T_{e(h)}$ is its branch-word tensor. The coordinate sets themselves need not be finite.
-- source:
--   https://prove2.me/submissions/facf5b05-d302-42c1-a107-8ff40a0c2134; OAI.MatrixMultiplication.AuxiliarySeparation.exactType_power_pullback, lines 15511-15531

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
import Definitions.Def_OAI429_GenericNumerics
import Definitions.Def_OAI429_GenericRank
import Definitions.Def_OAI429_GenericSeparation
import Definitions.Def_OAI429_GenericTags
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical
namespace OAIAllFieldsSeparation
end OAIAllFieldsSeparation

theorem OAI.MatrixMultiplication.AuxiliarySeparation.exactType_power_pullback.{u_1} :
    ∀ {𝕜 : Type u_1} [inst : Field 𝕜] [IsAlgClosed 𝕜] {s : ℕ} {X Y Z : Type}
  (B : Fin s → OAI.MatrixMultiplication.Foundation.Tensor 𝕜 X Y Z) (counts : Fin s → ℕ)
  (e :
    Fin (Fintype.card (OAI.MatrixMultiplication.Foundation.ExactWords counts)) ≃
      OAI.MatrixMultiplication.Foundation.ExactWords counts),
  OAI.MatrixMultiplication.Foundation.Tensor.pullback id
      (OAI.MatrixMultiplication.AuxiliarySeparation.typeWordCoordinate counts e)
      (OAI.MatrixMultiplication.AuxiliarySeparation.typeWordCoordinate counts e)
      ((OAIAllFieldsSeparation.sharedFirstTensor B).power (∑ a : Fin s, counts a)) =
    OAIAllFieldsSeparation.sharedFirstTensor
      fun (h : Fin (Fintype.card (OAI.MatrixMultiplication.Foundation.ExactWords counts))) =>
      OAI.MatrixMultiplication.AuxiliarySeparation.branchWordTensor B ↑(e h)
:= by sorry
