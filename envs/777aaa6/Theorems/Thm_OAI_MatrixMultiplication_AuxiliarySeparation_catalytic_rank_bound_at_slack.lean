-- Prove2me | Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_catalytic_rank_bound_at_slack
-- name    : OAI.MatrixMultiplication.AuxiliarySeparation.catalytic_rank_bound_at_slack
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:23:07.749+00:00
-- url     : https://prove2.me/theorems/713c855f-af6c-481f-9993-a7f2017e11f5
-- title:
--   A catalytic rank budget bounds exponential growth with slack
-- statement:
--   For a field $F$, let $R_F(n)$ be the exact rank of the square matrix multiplication coefficient tensor of size $n$, and let $\nu_F=\inf_{n\ge2}\log R_F(n)/\log n$. Fix $d,n,B,R\in\mathbb N$ with $d>0$ and $n\ge1$. Assume that for every $j\ge1$ and every $g\in\mathbb N$, the condition $R_F(g)\le n^j$ implies $R_F(d^jg)\le R B^j$. Then every real $\delta>0$ satisfies
--   \[
--   d^{\nu_F}n^{\nu_F/(\nu_F+\delta)}\le B.
--   \]
--   The overhead $R$ is fixed independently of the tensor-power index $j$. This converts a uniform catalytic rank comparison into an exponent inequality.
-- source:
--   https://prove2.me/submissions/facf5b05-d302-42c1-a107-8ff40a0c2134; OAI.MatrixMultiplication.AuxiliarySeparation.catalytic_rank_bound_at_slack, lines 8064-8121

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
import Definitions.Def_OAI429_GenericRank
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_exactMatrixRank_pow_le
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_floor_rank_power_bounds
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_le_of_eventually_pow_le_linear_mul_pow
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_matrixMultiplication_rankAtMost_cubic
import Theorems.Thm_OAI_MatrixMultiplication_Foundation_Tensor_RankAtMost_card_le_of_identity
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical

theorem OAI.MatrixMultiplication.AuxiliarySeparation.catalytic_rank_bound_at_slack.{u_1} :
    ∀ {𝕜 : Type u_1} [inst : Field 𝕜] {d n K R : ℕ},
  0 < d →
    1 ≤ n →
      (∀ (j : ℕ),
          1 ≤ j →
            ∀ (g : ℕ),
              OAI.MatrixMultiplication.AuxiliarySeparation.exactMatrixRank 𝕜 g ≤ n ^ j →
                OAI.MatrixMultiplication.AuxiliarySeparation.exactMatrixRank 𝕜 (d ^ j * g) ≤ R * K ^ j) →
        ∀ {δ : ℝ},
          0 < δ →
            HPow.hPow (α := ℝ) (↑d) (OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent 𝕜) *
                HPow.hPow (α := ℝ) (↑n)
                  (OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent 𝕜 /
                    (OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent 𝕜 + δ)) ≤
              ↑K
:= by sorry
