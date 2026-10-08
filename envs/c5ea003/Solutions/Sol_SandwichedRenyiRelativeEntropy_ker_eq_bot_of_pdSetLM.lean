-- Prove2me | solution 1 for SandwichedRenyiRelativeEntropy.ker_eq_bot_of_pdSetLM
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-08T01:43:21.552082+00:00
-- url     : https://prove2.me/submissions/f26a48f8-1652-45f1-94bb-66e0dcc536ae

import Mathlib.Algebra.Central.End
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Definitions.Def_CRCD_Quantum_QuantumEntropy_HaarUnitary
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedQuasiJensen_part_3
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiRelativeEntropy_part_3
import Definitions.Def_CRCD_Quantum_QuantumEntropy_TensorCFC
import Definitions.Def_CRCD_Quantum_QuantumEntropy_YoungInequality_part_2
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumChannel_part_4
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumState
import Definitions.Def_CRCD_Quantum_TraceInequality_BlockDiagonal
import Definitions.Def_CRCD_Quantum_TraceInequality_GeneralizedPerspectiveFunction
import Definitions.Def_CRCD_Quantum_TraceInequality_HilbertSchmidtOperatorSpace
import Definitions.Def_CRCD_Quantum_TraceInequality_JensenOperatorInequality
import Definitions.Def_CRCD_Quantum_TraceInequality_JensenOperatorInequalityIImpIV_part_2
import Definitions.Def_CRCD_Quantum_TraceInequality_LiebAndoTrace_part_2
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzCore_part_3
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzTheorem
import Definitions.Def_CRCD_Quantum_TraceInequality_OperatorGeometricMean

section

/-
Copyright (c) 2025-2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/




/-!
# Jensen–Haar inequality and monotonicity of the sandwiched Rényi divergence

This file proves the central Jensen-style inequality
(`sandwichedQuasi_jensen_haar`) underlying monotonicity of the sandwiched Rényi
divergence under CPTP maps, and the main monotonicity theorem
(`sandwichedRenyiDiv_monotone`).

The proof is structured in three layers:

1. `jensen_haar_core` — Frank–Lieb's central inequality before tensor
   multiplicativity collapses the LHS / RHS to `Re Q_α(E ρ‖E σ)` and
   `Re Q_α(ρ‖σ)`. Proved by passing to a closed convex sub-cone of `pdSetLM`
   cut out by explicit spectral bounds and applying Mathlib's Bochner-integral
   Jensen (`HaarUnitary.jointly_convex_integral_le` /
   `HaarUnitary.jointly_concave_le_integral`).

2. `sandwichedQuasi_jensen_haar` — the abstract Jensen–Haar interface, obtained
   from `jensen_haar_core` by tensor multiplicativity and the self-quasi
   identity `sandwichedQuasi α τ τ = Tr τ`.

3. `sandwichedRenyiDiv_monotone` — the main theorem
   `D_α(E ρ ‖ E σ) ≤ D_α(ρ ‖ σ)`, obtained from `sandwichedQuasi_jensen_haar`
   by applying the Stinespring dilation (`CPTP.exists_stinespring_dilation`)
   and the monotonic log transform.

The closed sub-cone construction in layer 1 uses
`CFC.exists_pos_algebraMap_le_iff` for the lower bound (positive spectrum gives
`∃ ε > 0, ε • 1 ≤ A`) and operator-norm bounds for the upper bound.
-/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel MeasureTheory HaarUnitary TensorProduct
open GeneralizedPerspectiveFunction
open scoped ComplexOrder NNReal Topology

universe u

set_option linter.style.longLine false



/-! ### Spectral bounds for operators in `pdSetLM` -/





/-! ### The closed convex sub-cone -/

























/-! ### Helper lemmas for the Form A Jensen–Haar proof -/

















/-! ### Positive-definite perturbations `A + ε • 1` (used for the cone arguments) -/











/-! ### Continuity / concavity of `Re Q_α` on the non-negative cone (`α < 1`) -/







section JointlyConvexNonneg
attribute [local irreducible] quasiVar



end JointlyConvexNonneg

section JointlyConcaveNonneg
-- `sandwichedQuasi` is treated as a black box here (only continuity, the pd Jensen
-- inequality, and limits are used), so making it irreducible avoids the unifier
-- unfolding the large CFC expression during def-eq checks.
attribute [local irreducible] sandwichedQuasi



end JointlyConcaveNonneg

section JensenHaarCore
-- `sandwichedQuasi`/`quasiVar` are treated as black boxes (only via lemmas), so making
-- them irreducible avoids the unifier unfolding their large CFC expressions during the
-- many `rw`/`isDefEq` checks in the proof.
attribute [local irreducible] sandwichedQuasi quasiVar



end JensenHaarCore

/-! ### The abstract Jensen-Haar interface -/



/-! ### Main monotonicity theorem -/



/-! ### Extension to non-negative operators (Frank–Lieb, arXiv:1306.5358 Thm 1)

The PDF formulates Theorem 1 for non-negative (rather than positive-definite)
operators `ρ, σ`. The natural extension is via perturbation: replace `ρ, σ` by
their pd perturbations `ρ + ε • 1`, `σ + ε • 1` for `ε > 0`. The existing
theorem applies whenever the four operators (`ρ + ε • 1`, `σ + ε • 1`,
`E (ρ + ε • 1)`, `E (σ + ε • 1)`) are all positive-definite.

For a **faithful** CPTP map `E` (i.e., `E 1` positive-definite), this is
automatic: by linearity of `E`, `E (ρ + ε • 1) = E ρ + ε • E 1`, which is a
non-negative operator plus a positive-definite operator, hence pd.

Below we add the helper lemmas (sum of nonneg and pd is pd, positive scalar
multiple of pd is pd, etc.) and then state the perturbed Theorem 1
`sandwichedRenyiDiv_monotone_nonneg_perturbed`. The "limit version"
(taking `ε → 0+`) requires continuity of `sandwichedRenyiDiv` at the boundary
of `pdSetLM`, which is finite when the kernels match and `+∞` otherwise.
-/







end SandwichedRenyiRelativeEntropy

open SandwichedRenyiRelativeEntropy
open QuantumState QuantumChannel MeasureTheory HaarUnitary TensorProduct
open GeneralizedPerspectiveFunction
open scoped ComplexOrder NNReal Topology
universe u
set_option linter.style.longLine false
open SandwichedRenyiRelativeEntropy in
/-- For `σ ∈ pdSetLM`, the kernel is trivial: `LinearMap.ker σ = ⊥`. -/
theorem solution
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {σ : L ℋ} (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    LinearMap.ker σ = ⊥ := by
  have h_unit : IsUnit σ := isUnit_of_pdSetLM hσ
  obtain ⟨u, hu⟩ := h_unit
  rw [LinearMap.ker_eq_bot]
  intro x y hxy
  -- `u.inv * σ = 1` in `L ℋ`; apply to both sides.
  have h_invσ : (u.inv : L ℋ) * σ = 1 := by rw [← hu]; exact u.inv_val
  -- For `f g : L ℋ` and `z : ℋ`, `(f * g) z = f (g z)` definitionally.
  have h_apply : ∀ z : ℋ, (u.inv : L ℋ) (σ z) = z := fun z => by
    have : ((u.inv : L ℋ) * σ) z = z := by rw [h_invσ]; rfl
    exact this
  rw [← h_apply x, ← h_apply y, hxy]

end
