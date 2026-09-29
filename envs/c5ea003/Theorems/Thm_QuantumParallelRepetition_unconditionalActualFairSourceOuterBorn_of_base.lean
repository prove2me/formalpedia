-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceOuterBorn_of_base
-- name    : QuantumParallelRepetition.unconditionalActualFairSourceOuterBorn_of_base
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T19:02:25.619757+00:00
-- url     : https://prove2.me/theorems/11cb43db-bc37-444a-ad01-38d0beb07565
-- title:
--   Dilating a state by the phase and retained registers scales the Born value by its mass
-- statement:
--   Keep the setting of the previous lemma and additionally fix a phase count $P \ge 1$, a grid $N \ge 1$, a harmonic
--   parameter $m \ge 1$, a horizon $L$ with stage index $j$, a constant width function on one stage, a unit vector
--   $\psi$ on the doubled global-history register, and a real number $v$. Assume the *base* Born identity
--   $\langle \overline{\psi},\, W_{x,y}\,\overline{\psi}\rangle = v$ for the bare verifier effect $W_{x,y}$.
--   Let $\Psi_j$ be the dilated stage-$j$ source vector, obtained by tensoring the coherent phase state built from
--   $\overline{\psi}$ and the embezzlement states of size $Nm$ with the normalized diagonal work vector of stage $j$,
--   and let $\widehat{W}_j$ be the corresponding dilated verifier effect (the same predicate sum, now with the selected
--   POVMs, tensored with the identity on the retained register). Then
--   $$\bigl\langle \Psi_j,\, \widehat{W}_j\, \Psi_j \bigr\rangle \;=\; \|\Psi_j\|^2 \cdot v ,$$
--   so the dilation changes the Born value only by the mass of the branch it lands in.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L64482-L64572

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_26
import Theorems.Thm_QuantumParallelRepetition_exactAlicePurificationFamily_posSemidef
import Theorems.Thm_QuantumParallelRepetition_exactBobPurificationFamily_posSemidef
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.FinEnum
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem QuantumParallelRepetition.unconditionalActualFairSourceOuterBorn_of_base
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (phases : 0 < P) (grid : 0 < N)
    (harmonic : 0 < m)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (ξ ζ : BipartiteUnitVector
      (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)))
    (ψ : EuclideanSpace ℂ
      (Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) ×
       Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))))
    (ψ_unit : ‖ψ‖ = 1)
    (j : Fin L) (x : X) (y : Y) (value : ℝ)
    (base_born :
      quadraticExpectation
        (unconditionalActualFairSourceBaseWinningCLM
          G n S D a₀ b₀ x y)
        (unconditionalConjugatePureVector ψ) = value) :
    quadraticExpectation
      (integratorActualC485WinningEffect
        G n S D a₀ b₀ (P := P) (N := N) (m := m) j x y)
      (integratorActualC485SourceVector
        (B := P) (N := N) (m := m) width schedule ξ ζ ψ j) =
      ‖integratorActualC485SourceVector
        (B := P) (N := N) (m := m) width schedule ξ ζ ψ j‖ ^ 2 * value := by sorry
