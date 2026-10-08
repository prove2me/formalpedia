-- Prove2me | Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedQuasiJensen_part_2
-- name    : CRCD_Quantum_QuantumEntropy_SandwichedQuasiJensen_part_2
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T01:21:39.917539+00:00
-- url     : https://prove2.me/theorems/51779340-12e3-45be-a2d5-3e21324a1992
-- title:
--   Jensen–Haar inequalities on singular and faithful operator domains
-- statement:
--   Let the spaces involved be nonzero finite-dimensional complex Hilbert spaces. On the full positive semidefinite cone, including singular operators, $\operatorname{Re}Q_\alpha$ is jointly concave for $1/2\le\alpha<1$, while $\operatorname{Re}V_\alpha(\rho,\sigma;X)$ is jointly convex for $\alpha>1$ and fixed positive-definite $X$.
--
--   Let $V:H\to K\otimes E$ satisfy $V^*V=I_H$, and put $\Phi(\gamma)=\operatorname{Tr}_E(V\gamma V^*)$. For $\alpha\ge1/2$, $\alpha\ne1$, positive-definite $\rho,\sigma$ and positive-definite $\Phi(\rho),\Phi(\sigma)$, the part proves
--   $$
--   \bigl[\operatorname{Re}Q_\alpha(\Phi(\rho)\Vert\Phi(\sigma))
--   -\operatorname{Re}Q_\alpha(\rho\Vert\sigma)\bigr](\alpha-1)\le0.
--   $$
--   The inner form has $\Phi(\rho)\otimes\tau_E,\Phi(\sigma)\otimes\tau_E$ in the first quasi-entropy and $V\rho V^*,V\sigma V^*$ in the second, where $\tau_E=I_E/\dim E$. Its inequality has the same factor $\alpha-1$. The isometric outputs can be rank deficient; the positive-definiteness assumptions apply to the input pair and the partial-trace pair. The trace functionals here are finite complex quantities with their real parts taken explicitly, and no trace-one normalization is assumed. This part does not assert joint continuity or joint convexity of $Q_\alpha$ on the singular cone for $\alpha>1$.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumEntropy/SandwichedQuasiJensen.lean#L813-L1402

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
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedQuasiJensen_part_1
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

/-- Joint convexity of `(ρ, σ) ↦ Re quasiVar α ρ σ H` extends from `pdSetLM` to the whole
    non-negative cone (fixed pd `H`, `α > 1`), by the same `ε → 0⁺` perturbation + joint
    continuity (`quasiVar_re_continuousOn_nonneg`) argument as the concave case. -/
 lemma quasiVar_re_jointlyConvex_nonneg {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {α : ℝ} (hα : 1 < α) {H : L 𝒦} (hH : H ∈ pdSetLM (ℋ := 𝒦)) :
    JointlyConvexOn {A : L 𝒦 | (0 : L 𝒦) ≤ A} {A : L 𝒦 | (0 : L 𝒦) ≤ A}
      (fun ρ σ => (quasiVar (ℋ := 𝒦) α ρ σ H).re) := by
  have hcont := _root_.SandwichedRenyiRelativeEntropy.quasiVar_re_continuousOn_nonneg (𝒦 := 𝒦) hα (nonneg_of_pdSetLM hH)
  have hpd := quasiVar_re_jointlyConvex_pdSetLM (ℋ := 𝒦) hα hH
  intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  simp only [Set.mem_setOf_eq] at hρ₁ hρ₂ hσ₁ hσ₂
  have key : ∀ a b : L 𝒦, (0 : L 𝒦) ≤ a → (0 : L 𝒦) ≤ b →
      Filter.Tendsto
        (fun ε : ℝ => (quasiVar α (a + (ε : ℂ) • 1) (b + (ε : ℂ) • 1) H).re)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (quasiVar α a b H).re) := by
    intro a b ha hb
    have hcurve : Continuous (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1)) := by fun_prop
    have h_into : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1) ∈
          ({A : L 𝒦 | (0 : L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0 : L 𝒦) ≤ A}) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      have hsmul : (0 : L 𝒦) ≤ (ε : ℂ) • (1 : L 𝒦) :=
        nonneg_of_pdSetLM (pos_smul_one_pdSetLM hε')
      exact ⟨by simpa using add_nonneg ha hsmul, by simpa using add_nonneg hb hsmul⟩
    have h_tendsto_curve :
        Filter.Tendsto (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhdsWithin (a, b) ({A : L 𝒦 | (0:L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0:L 𝒦) ≤ A})) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, h_into⟩
      have h0 : Filter.Tendsto (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1))
          (nhds (0 : ℝ)) (nhds (a, b)) := by
        have h := hcurve.tendsto 0; simpa using h
      exact h0.mono_left nhdsWithin_le_nhds
    have hcwa : Filter.Tendsto
        (Function.uncurry (fun ρ σ : L 𝒦 => (quasiVar α ρ σ H).re))
        (nhdsWithin (a, b) ({A : L 𝒦 | (0:L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0:L 𝒦) ≤ A}))
        (nhds (quasiVar α a b H).re) :=
      hcont (a, b) ⟨ha, hb⟩
    exact hcwa.comp h_tendsto_curve
  have hρc : (0 : L 𝒦) ≤ (1 - θ) • ρ₁ + θ • ρ₂ :=
    add_nonneg (smul_nonneg (by linarith) hρ₁) (smul_nonneg hθ0 hρ₂)
  have hσc : (0 : L 𝒦) ≤ (1 - θ) • σ₁ + θ • σ₂ :=
    add_nonneg (smul_nonneg (by linarith) hσ₁) (smul_nonneg hθ0 hσ₂)
  have hcombo : ∀ a₁ a₂ : L 𝒦, ∀ ε : ℝ,
      ((1 - θ) • a₁ + θ • a₂) + (ε : ℂ) • 1 =
        (1 - θ) • (a₁ + (ε : ℂ) • 1) + θ • (a₂ + (ε : ℂ) • 1) := by
    intro a₁ a₂ ε
    have h1 : ((1 - θ : ℝ)) • ((ε : ℂ) • (1 : L 𝒦)) + (θ : ℝ) • ((ε : ℂ) • (1 : L 𝒦)) =
        (ε : ℂ) • (1 : L 𝒦) := by
      rw [← add_smul]; norm_num
    simp only [smul_add]
    rw [show (1 - θ) • a₁ + (1 - θ) • (ε : ℂ) • 1 + (θ • a₂ + θ • (ε : ℂ) • 1) =
        ((1 - θ) • a₁ + θ • a₂) + ((1 - θ) • (ε : ℂ) • 1 + θ • (ε : ℂ) • 1) from by abel,
        h1]
  refine le_of_tendsto_of_tendsto (key _ _ hρc hσc)
    (((key ρ₁ σ₁ hρ₁ hσ₁).const_smul (1 - θ)).add ((key ρ₂ σ₂ hρ₂ hσ₂).const_smul θ)) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  have hp₁ := nonneg_add_pos_smul_one_pdSetLM hρ₁ hε'
  have hp₂ := nonneg_add_pos_smul_one_pdSetLM hρ₂ hε'
  have hq₁ := nonneg_add_pos_smul_one_pdSetLM hσ₁ hε'
  have hq₂ := nonneg_add_pos_smul_one_pdSetLM hσ₂ hε'
  have hj := hpd hp₁ hp₂ hq₁ hq₂ hθ0 hθ1
  rw [hcombo ρ₁ ρ₂ ε, hcombo σ₁ σ₂ ε]
  exact hj

end JointlyConvexNonneg

section JointlyConcaveNonneg
-- `sandwichedQuasi` is treated as a black box here (only continuity, the pd Jensen
-- inequality, and limits are used), so making it irreducible avoids the unifier
-- unfolding the large CFC expression during def-eq checks.
attribute [local irreducible] sandwichedQuasi

/-- **Proposition 3 on the non-negative cone (concave case, `1/2 ≤ α < 1`).**
    Joint concavity of `(ρ, σ) ↦ Re Q_α(ρ‖σ)` extends from `pdSetLM` to the whole
    non-negative cone by an `ε → 0⁺` perturbation `(ρ, σ) ↦ (ρ + ε•1, σ + ε•1)`, using
    joint continuity on the cone (`sandwichedQuasi_re_continuousOn_nonneg`). -/
 lemma sandwichedQuasi_re_jointlyConcave_nonneg {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {α : ℝ} (hα_ge : 1 / 2 ≤ α) (hα_lt : α < 1) :
    JointlyConcaveOn {A : L 𝒦 | (0 : L 𝒦) ≤ A} {A : L 𝒦 | (0 : L 𝒦) ≤ A}
      (fun ρ σ => (sandwichedQuasi (ℋ := 𝒦) α ρ σ).re) := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hcont := _root_.QCProve2mePrivate.Quantum_QuantumEntropy_SandwichedQuasiJensen_sandwichedQuasi_re_continuousOn_nonneg (𝒦 := 𝒦) hα0 hα_lt
  have hpd := sandwichedQuasi_re_jointlyConcave (ℋ := 𝒦) hα_ge hα_lt
  intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  simp only [Set.mem_setOf_eq] at hρ₁ hρ₂ hσ₁ hσ₂
  -- Limit of `Re Q_α` at a non-negative pair, approached through pd perturbations `+ ε•1`.
  have key : ∀ a b : L 𝒦, (0 : L 𝒦) ≤ a → (0 : L 𝒦) ≤ b →
      Filter.Tendsto
        (fun ε : ℝ => (sandwichedQuasi α (a + (ε : ℂ) • 1) (b + (ε : ℂ) • 1)).re)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (sandwichedQuasi α a b).re) := by
    intro a b ha hb
    have hcurve : Continuous (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1)) := by fun_prop
    have h_into : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1) ∈
          ({A : L 𝒦 | (0 : L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0 : L 𝒦) ≤ A}) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      have hsmul : (0 : L 𝒦) ≤ (ε : ℂ) • (1 : L 𝒦) :=
        nonneg_of_pdSetLM (pos_smul_one_pdSetLM hε')
      exact ⟨by simpa using add_nonneg ha hsmul, by simpa using add_nonneg hb hsmul⟩
    have h_tendsto_curve :
        Filter.Tendsto (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhdsWithin (a, b) ({A : L 𝒦 | (0:L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0:L 𝒦) ≤ A})) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, h_into⟩
      have h0 : Filter.Tendsto (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1))
          (nhds (0 : ℝ)) (nhds (a, b)) := by
        have h := hcurve.tendsto 0; simpa using h
      exact h0.mono_left nhdsWithin_le_nhds
    have hcwa : Filter.Tendsto
        (Function.uncurry (fun ρ σ : L 𝒦 => (sandwichedQuasi α ρ σ).re))
        (nhdsWithin (a, b) ({A : L 𝒦 | (0:L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0:L 𝒦) ≤ A}))
        (nhds (sandwichedQuasi α a b).re) :=
      hcont (a, b) ⟨ha, hb⟩
    exact hcwa.comp h_tendsto_curve
  -- Non-negativity of the convex combinations.
  have hρc : (0 : L 𝒦) ≤ (1 - θ) • ρ₁ + θ • ρ₂ :=
    add_nonneg (smul_nonneg (by linarith) hρ₁) (smul_nonneg hθ0 hρ₂)
  have hσc : (0 : L 𝒦) ≤ (1 - θ) • σ₁ + θ • σ₂ :=
    add_nonneg (smul_nonneg (by linarith) hσ₁) (smul_nonneg hθ0 hσ₂)
  -- The perturbed convex combination equals the convex combination of perturbations.
  have hcombo : ∀ a₁ a₂ : L 𝒦, ∀ ε : ℝ,
      ((1 - θ) • a₁ + θ • a₂) + (ε : ℂ) • 1 =
        (1 - θ) • (a₁ + (ε : ℂ) • 1) + θ • (a₂ + (ε : ℂ) • 1) := by
    intro a₁ a₂ ε
    have h1 : ((1 - θ : ℝ)) • ((ε : ℂ) • (1 : L 𝒦)) + (θ : ℝ) • ((ε : ℂ) • (1 : L 𝒦)) =
        (ε : ℂ) • (1 : L 𝒦) := by
      rw [← add_smul]; norm_num
    simp only [smul_add]
    rw [show (1 - θ) • a₁ + (1 - θ) • (ε : ℂ) • 1 + (θ • a₂ + θ • (ε : ℂ) • 1) =
        ((1 - θ) • a₁ + θ • a₂) + ((1 - θ) • (ε : ℂ) • 1 + θ • (ε : ℂ) • 1) from by abel,
        h1]
  -- Pass the pd Jensen inequality to the limit `ε → 0⁺`.
  refine le_of_tendsto_of_tendsto
    (((key ρ₁ σ₁ hρ₁ hσ₁).const_smul (1 - θ)).add ((key ρ₂ σ₂ hρ₂ hσ₂).const_smul θ))
    (key _ _ hρc hσc) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  have hp₁ := nonneg_add_pos_smul_one_pdSetLM hρ₁ hε'
  have hp₂ := nonneg_add_pos_smul_one_pdSetLM hρ₂ hε'
  have hq₁ := nonneg_add_pos_smul_one_pdSetLM hσ₁ hε'
  have hq₂ := nonneg_add_pos_smul_one_pdSetLM hσ₂ hε'
  have hj := hpd hp₁ hp₂ hq₁ hq₂ hθ0 hθ1
  rw [hcombo ρ₁ ρ₂ ε, hcombo σ₁ σ₂ ε]
  exact hj

end JointlyConcaveNonneg

section JensenHaarCore
-- `sandwichedQuasi`/`quasiVar` are treated as black boxes (only via lemmas), so making
-- them irreducible avoids the unifier unfolding their large CFC expressions during the
-- many `rw`/`isDefEq` checks in the proof.
attribute [local irreducible] sandwichedQuasi quasiVar

set_option maxHeartbeats 800000 in
-- The `α > 1` branch is a long variational assembly (Jensen on `quasiVar`, pointwise
-- bound, twirl); even with the irreducibility above it needs a raised heartbeat budget.
/-- **Inner Jensen–Haar inequality (Form A, isometric Stinespring).**

    Reformulation of the central Jensen-style inequality in terms of an
    *isometric* Stinespring map `V : ℋ →ₗ[ℂ] (ℋ ⊗ ℋ_env)` with `V*V = I`,
    rather than the previous unitary-with-mixed-environment Form B
    (`Tr₂[U(τ ⊗ γ)U*]`). The inequality states:

    `Re sandwichedQuasi α ((E ρ) ⊗ τ_max) ((E σ) ⊗ τ_max)`
    `⋚ Re sandwichedQuasi α (V ρ V*) (V σ V*)`

    where `E γ := TrRight (V γ V*)` and `τ_max := (dim ℋ_env)⁻¹ • 1` on
    `ℋ_env`; direction `≤` for `α > 1`, `≥` for `α ∈ [1/2, 1)`.

    **Proof (Frank–Lieb arXiv:1306.5358, isometric variant).**
    The integrand `g_ρ u := (1_ℋ ⊗ u) · (V ρ V*) · (1_ℋ ⊗ u*)` is in general
    *rank-deficient* (supported on the range of `V V*`), so the original
    closed-pd-subcone Jensen argument no longer applies directly. We instead
    work on the whole non-negative cone `{A | 0 ≤ A}` (closed and convex):
      1. The right-twirl identity (`right_twirl_eq`, the `TrRight` analogue of
         `HaarUnitary.twirl_eq_partialTrace_smul_id`) identifies
         `∫ g_ρ u du = (E ρ) ⊗ τ_max`.
      2. `g_ρ u` is non-negative (unitary conjugation of `V ρ V* ≥ 0`) and
         `Re Q_α` is jointly concave (`α < 1`) / convex (`α > 1`) and continuous
         on the non-negative cone.
      3. Bochner–Jensen (`jointly_concave_le_integral`) plus unitary invariance
         of `Q_α` (the integrand `Re Q_α(g_ρ u, g_σ u)` is *constant*
         `= Re Q_α(V ρ V*, V σ V*)`) gives the inequality.

    **Both cases are proved.** The `α ∈ [1/2, 1)` (concave) branch applies
    Bochner–Jensen to `Re Q_α` directly. For `α > 1` the exponent
    `β = (1-α)/(2α) < 0` makes `Re Q_α` discontinuous at singular `σ`, so joint
    convexity on the non-negative cone is unavailable; instead we use the
    Frank–Lieb variational functional `quasiVar`: at the (pd) integral point
    `Q_α = quasiVar(·,·,H*)` for the optimizer `H*`, `quasiVar(·,·,H*)` is jointly
    convex and continuous on the psd cone (only positive exponents of `σ`), and
    pointwise `quasiVar(g_ρ u, g_σ u, H*) ≤ Q_α(g_ρ u, g_σ u)` — reduced through
    the single isometry `(1 ⊗ u) ∘ V` to `quasiVar_le_quasi` on the pd pair. -/
 theorem jensen_haar_core
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {ℋ_env : Type u} [Qudit ℋ_env] [Nontrivial ℋ_env]
    {α : ℝ} (_hα_ge : (1 : ℝ) / 2 ≤ α) (_hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ}
    (_hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (_hσ : σ ∈ pdSetLM (ℋ := ℋ))
    (V : ℋ →ₗ[ℂ] (𝒦 ⊗[ℂ] ℋ_env))
    (_hV : (LinearMap.adjoint V).comp V = (1 : L ℋ))
    (_hEρ : TrRight ((V.comp ρ).comp (LinearMap.adjoint V)) ∈ pdSetLM (ℋ := 𝒦))
    (_hEσ : TrRight ((V.comp σ).comp (LinearMap.adjoint V)) ∈ pdSetLM (ℋ := 𝒦)) :
    ((sandwichedQuasi α
        (TensorProduct.map
          (TrRight ((V.comp ρ).comp (LinearMap.adjoint V)))
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))
        (TensorProduct.map
          (TrRight ((V.comp σ).comp (LinearMap.adjoint V)))
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))).re -
      (sandwichedQuasi α
        ((V.comp ρ).comp (LinearMap.adjoint V))
        ((V.comp σ).comp (LinearMap.adjoint V))).re) * (α - 1) ≤ 0 := by
  -- `ℋ ⊗ ℋ_env` is again a (nontrivial) qudit.
  haveI : Nontrivial (𝒦 ⊗[ℂ] ℋ_env) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by
      rw [Module.finrank_tensorProduct]
      exact Nat.mul_pos (Module.finrank_pos) (Module.finrank_pos))
  rcases lt_or_gt_of_ne _hα_ne1 with hα_lt | hα_gt
  · -- **α ∈ [1/2, 1): concave Jensen–Haar.**
    -- Strategy: the Haar integrand `gρ u = (1⊗u)(VρV*)(1⊗u*)` is non-negative and
    -- `Re Q_α` is jointly concave + continuous on the whole non-negative cone, so
    -- Bochner–Jensen gives `∫ Re Q_α(gρ, gσ) ≤ Re Q_α(∫gρ, ∫gσ)`. The integrand is
    -- constant (`= Re Q_α(VρV*, VσV*)` by unitary invariance) and `∫gρ = Eρ ⊗ τmax`
    -- (right twirl), yielding `Re Q_α(VρV*, VσV*) ≤ Re Q_α(Eρ⊗τmax, Eσ⊗τmax)`.
    have hα0 : (0 : ℝ) < α := by linarith
    set Xρ : L (𝒦 ⊗[ℂ] ℋ_env) := (V.comp ρ).comp (LinearMap.adjoint V) with hXρ_def
    set Xσ : L (𝒦 ⊗[ℂ] ℋ_env) := (V.comp σ).comp (LinearMap.adjoint V) with hXσ_def
    have hρ_nn : (0 : L ℋ) ≤ ρ := nonneg_of_pdSetLM _hρ
    have hσ_nn : (0 : L ℋ) ≤ σ := nonneg_of_pdSetLM _hσ
    have hXρ_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Xρ := by
      rw [hXρ_def, LinearMap.nonneg_iff_isPositive]
      exact ((LinearMap.nonneg_iff_isPositive ρ).mp hρ_nn).conj_adjoint V
    have hXσ_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Xσ := by
      rw [hXσ_def, LinearMap.nonneg_iff_isPositive]
      exact ((LinearMap.nonneg_iff_isPositive σ).mp hσ_nn).conj_adjoint V
    -- Haar integrands.
    set gρ : unitary (L ℋ_env) → L (𝒦 ⊗[ℂ] ℋ_env) := fun u =>
        TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)) * Xρ *
          TensorProduct.map (LinearMap.id (M := 𝒦)) (star (u : L ℋ_env)) with hgρ_def
    set gσ : unitary (L ℋ_env) → L (𝒦 ⊗[ℂ] ℋ_env) := fun u =>
        TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)) * Xσ *
          TensorProduct.map (LinearMap.id (M := 𝒦)) (star (u : L ℋ_env)) with hgσ_def
    -- The integrand of `Re Q_α` is constant (unitary invariance of `Q_α`).
    have h_inv : ∀ u : unitary (L ℋ_env),
        (sandwichedQuasi α (gρ u) (gσ u)).re = (sandwichedQuasi α Xρ Xσ).re := by
      intro u
      set U : unitary (L (𝒦 ⊗[ℂ] ℋ_env)) :=
        ⟨TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)),
          _root_.SandwichedRenyiRelativeEntropy.tensorMap_right_unitary_of_unitary u⟩ with hU_def
      have hUcoe : ((U : unitary (L (𝒦 ⊗[ℂ] ℋ_env))) : L (𝒦 ⊗[ℂ] ℋ_env)) =
          TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)) := rfl
      have hUstar : ((star U : unitary (L (𝒦 ⊗[ℂ] ℋ_env))) : L (𝒦 ⊗[ℂ] ℋ_env)) =
          TensorProduct.map (LinearMap.id (M := 𝒦)) (star (u : L ℋ_env)) := by
        rw [Unitary.coe_star, hUcoe, _root_.SandwichedRenyiRelativeEntropy.tensorMap_right_star]
      have hgρ_eq : gρ u =
          (U : L (𝒦 ⊗[ℂ] ℋ_env)) * Xρ * (star U : L (𝒦 ⊗[ℂ] ℋ_env)) := by
        simp only [hgρ_def, hUcoe, _root_.SandwichedRenyiRelativeEntropy.tensorMap_right_star]
      have hgσ_eq : gσ u =
          (U : L (𝒦 ⊗[ℂ] ℋ_env)) * Xσ * (star U : L (𝒦 ⊗[ℂ] ℋ_env)) := by
        simp only [hgσ_def, hUcoe, _root_.SandwichedRenyiRelativeEntropy.tensorMap_right_star]
      rw [hgρ_eq, hgσ_eq, sandwichedQuasi_unitary_conj α Xρ Xσ U]
    -- Non-negativity of the integrands (the cone membership for Jensen).
    have hgρ_mem : ∀ᵐ u ∂(haarUnitary ℋ_env),
        gρ u ∈ {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} := by
      filter_upwards with u
      show (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ gρ u
      have h := star_left_conjugate_nonneg hXρ_nn
          (star (TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env))))
      rw [star_star, _root_.SandwichedRenyiRelativeEntropy.tensorMap_right_star] at h
      exact h
    have hgσ_mem : ∀ᵐ u ∂(haarUnitary ℋ_env),
        gσ u ∈ {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} := by
      filter_upwards with u
      show (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ gσ u
      have h := star_left_conjugate_nonneg hXσ_nn
          (star (TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env))))
      rw [star_star, _root_.SandwichedRenyiRelativeEntropy.tensorMap_right_star] at h
      exact h
    -- Integrability.
    have hgρ_int : Integrable gρ (haarUnitary ℋ_env) :=
      integrable_unitaryConj_tensor_right Xρ
    have hgσ_int : Integrable gσ (haarUnitary ℋ_env) :=
      integrable_unitaryConj_tensor_right Xσ
    have hfg_int :
        Integrable (fun u => (sandwichedQuasi α (gρ u) (gσ u)).re) (haarUnitary ℋ_env) := by
      simp_rw [h_inv]; exact integrable_const _
    -- The two integrals collapse via the right twirl.
    have hint_ρ : (∫ u, gρ u ∂(haarUnitary ℋ_env)) =
        TensorProduct.map (TrRight Xρ)
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) :=
      _root_.SandwichedRenyiRelativeEntropy.right_twirl_eq Xρ
    have hint_σ : (∫ u, gσ u ∂(haarUnitary ℋ_env)) =
        TensorProduct.map (TrRight Xσ)
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) :=
      _root_.SandwichedRenyiRelativeEntropy.right_twirl_eq Xσ
    -- The constant-integrand integral equals `Re Q_α(VρV*, VσV*)`.
    have h_lhs_int : (∫ u, (sandwichedQuasi α (gρ u) (gσ u)).re ∂(haarUnitary ℋ_env))
        = (sandwichedQuasi α Xρ Xσ).re := by
      simp_rw [h_inv]; simp
    -- Membership of the (collapsed) integrals in the closed convex cone.
    have hmem_ρ : (∫ u, gρ u ∂(haarUnitary ℋ_env)) ∈
        {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} :=
      _root_.SandwichedRenyiRelativeEntropy.convex_nonneg_cone.integral_mem _root_.SandwichedRenyiRelativeEntropy.isClosed_nonneg_cone hgρ_mem hgρ_int
    have hmem_σ : (∫ u, gσ u ∂(haarUnitary ℋ_env)) ∈
        {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} :=
      _root_.SandwichedRenyiRelativeEntropy.convex_nonneg_cone.integral_mem _root_.SandwichedRenyiRelativeEntropy.isClosed_nonneg_cone hgσ_mem hgσ_int
    -- Bochner–Jensen on the non-negative cone.
    have hJ := jointly_concave_le_integral (μ := haarUnitary ℋ_env)
      _root_.SandwichedRenyiRelativeEntropy.convex_nonneg_cone _root_.SandwichedRenyiRelativeEntropy.convex_nonneg_cone _root_.SandwichedRenyiRelativeEntropy.isClosed_nonneg_cone _root_.SandwichedRenyiRelativeEntropy.isClosed_nonneg_cone
      (_root_.SandwichedRenyiRelativeEntropy.sandwichedQuasi_re_jointlyConcave_nonneg _hα_ge hα_lt)
      (_root_.QCProve2mePrivate.Quantum_QuantumEntropy_SandwichedQuasiJensen_sandwichedQuasi_re_continuousOn_nonneg hα0 hα_lt)
      hgρ_mem hgσ_mem hgρ_int hgσ_int hfg_int hmem_ρ hmem_σ
    rw [h_lhs_int, hint_ρ, hint_σ] at hJ
    -- `hJ : Re Q_α(VρV*, VσV*) ≤ Re Q_α(Eρ⊗τmax, Eσ⊗τmax)`; close with the sign of `α-1`.
    have hα1_neg : α - 1 ≤ 0 := by linarith
    have hD : (0 : ℝ) ≤ (sandwichedQuasi α
        (TensorProduct.map (TrRight Xρ) ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))
        (TensorProduct.map (TrRight Xσ)
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))).re -
        (sandwichedQuasi α Xρ Xσ).re := sub_nonneg.mpr hJ
    nlinarith [hD, hα1_neg, mul_nonneg hD (neg_nonneg.mpr hα1_neg)]
  · -- **α > 1: convex case, via the Frank–Lieb variational functional `quasiVar`.**
    -- `Re Q_α` is discontinuous at singular `σ`, so we cannot apply Jensen to it directly.
    -- Instead we use that at the (pd) integral point `Pρ = ∫gρ`, `Pσ = ∫gσ`,
    -- `Re Q_α(Pρ,Pσ) = Re quasiVar(Pρ,Pσ,H*)` for the optimizer `H*`, that
    -- `quasiVar(·,·,H*)` IS jointly convex + continuous on the psd cone (positive
    -- exponents), and that pointwise `quasiVar(gρu,gσu,H*) ≤ Q_α(gρu,gσu)` (reduced via
    -- the single isometry `(1⊗u)∘V` to `quasiVar_le_quasi` on the pd pair `ρ,σ`).
    have hα0 : (0 : ℝ) < α := by linarith
    have hα_ne1 : α ≠ 1 := ne_of_gt hα_gt
    set Xρ : L (𝒦 ⊗[ℂ] ℋ_env) := (V.comp ρ).comp (LinearMap.adjoint V) with hXρ_def
    set Xσ : L (𝒦 ⊗[ℂ] ℋ_env) := (V.comp σ).comp (LinearMap.adjoint V) with hXσ_def
    have hρ_nn : (0 : L ℋ) ≤ ρ := nonneg_of_pdSetLM _hρ
    have hσ_nn : (0 : L ℋ) ≤ σ := nonneg_of_pdSetLM _hσ
    have hXρ_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Xρ := by
      rw [hXρ_def, LinearMap.nonneg_iff_isPositive]
      exact ((LinearMap.nonneg_iff_isPositive ρ).mp hρ_nn).conj_adjoint V
    have hXσ_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Xσ := by
      rw [hXσ_def, LinearMap.nonneg_iff_isPositive]
      exact ((LinearMap.nonneg_iff_isPositive σ).mp hσ_nn).conj_adjoint V
    set gρ : unitary (L ℋ_env) → L (𝒦 ⊗[ℂ] ℋ_env) := fun u =>
        TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)) * Xρ *
          TensorProduct.map (LinearMap.id (M := 𝒦)) (star (u : L ℋ_env)) with hgρ_def
    set gσ : unitary (L ℋ_env) → L (𝒦 ⊗[ℂ] ℋ_env) := fun u =>
        TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)) * Xσ *
          TensorProduct.map (LinearMap.id (M := 𝒦)) (star (u : L ℋ_env)) with hgσ_def
    -- Unitary invariance: the `Re Q_α` integrand is constant.
    have h_inv : ∀ u : unitary (L ℋ_env),
        (sandwichedQuasi α (gρ u) (gσ u)).re = (sandwichedQuasi α Xρ Xσ).re := by
      intro u
      set U : unitary (L (𝒦 ⊗[ℂ] ℋ_env)) :=
        ⟨TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)),
          _root_.SandwichedRenyiRelativeEntropy.tensorMap_right_unitary_of_unitary u⟩ with hU_def
      have hUcoe : ((U : unitary (L (𝒦 ⊗[ℂ] ℋ_env))) : L (𝒦 ⊗[ℂ] ℋ_env)) =
          TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)) := rfl
      have hgρ_eq : gρ u =
          (U : L (𝒦 ⊗[ℂ] ℋ_env)) * Xρ * (star U : L (𝒦 ⊗[ℂ] ℋ_env)) := by
        simp only [hgρ_def, hUcoe, _root_.SandwichedRenyiRelativeEntropy.tensorMap_right_star]
      have hgσ_eq : gσ u =
          (U : L (𝒦 ⊗[ℂ] ℋ_env)) * Xσ * (star U : L (𝒦 ⊗[ℂ] ℋ_env)) := by
        simp only [hgσ_def, hUcoe, _root_.SandwichedRenyiRelativeEntropy.tensorMap_right_star]
      rw [hgρ_eq, hgσ_eq, sandwichedQuasi_unitary_conj α Xρ Xσ U]
    -- Non-negativity of the integrands (everywhere).
    have hgρ_nn_all : ∀ u, gρ u ∈ {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} := by
      intro u
      change (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ gρ u
      have h := star_left_conjugate_nonneg hXρ_nn
          (star (TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env))))
      rw [star_star, _root_.SandwichedRenyiRelativeEntropy.tensorMap_right_star] at h
      exact h
    have hgσ_nn_all : ∀ u, gσ u ∈ {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} := by
      intro u
      change (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ gσ u
      have h := star_left_conjugate_nonneg hXσ_nn
          (star (TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env))))
      rw [star_star, _root_.SandwichedRenyiRelativeEntropy.tensorMap_right_star] at h
      exact h
    have hgρ_mem : ∀ᵐ u ∂(haarUnitary ℋ_env),
        gρ u ∈ {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} :=
      Filter.Eventually.of_forall hgρ_nn_all
    have hgσ_mem : ∀ᵐ u ∂(haarUnitary ℋ_env),
        gσ u ∈ {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} :=
      Filter.Eventually.of_forall hgσ_nn_all
    -- Integrability of the integrands and of the `Re Q_α` integrand.
    have hgρ_int : Integrable gρ (haarUnitary ℋ_env) := integrable_unitaryConj_tensor_right Xρ
    have hgσ_int : Integrable gσ (haarUnitary ℋ_env) := integrable_unitaryConj_tensor_right Xσ
    have hfg_int :
        Integrable (fun u => (sandwichedQuasi α (gρ u) (gσ u)).re) (haarUnitary ℋ_env) := by
      simp_rw [h_inv]; exact integrable_const _
    -- Right-twirl collapse of the integrals.
    have hint_ρ : (∫ u, gρ u ∂(haarUnitary ℋ_env)) =
        TensorProduct.map (TrRight Xρ)
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) := _root_.SandwichedRenyiRelativeEntropy.right_twirl_eq Xρ
    have hint_σ : (∫ u, gσ u ∂(haarUnitary ℋ_env)) =
        TensorProduct.map (TrRight Xσ)
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) := _root_.SandwichedRenyiRelativeEntropy.right_twirl_eq Xσ
    have h_lhs_int : (∫ u, (sandwichedQuasi α (gρ u) (gσ u)).re ∂(haarUnitary ℋ_env))
        = (sandwichedQuasi α Xρ Xσ).re := by simp_rw [h_inv]; simp
    have hmem_ρ : (∫ u, gρ u ∂(haarUnitary ℋ_env)) ∈
        {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} :=
      _root_.SandwichedRenyiRelativeEntropy.convex_nonneg_cone.integral_mem _root_.SandwichedRenyiRelativeEntropy.isClosed_nonneg_cone hgρ_mem hgρ_int
    have hmem_σ : (∫ u, gσ u ∂(haarUnitary ℋ_env)) ∈
        {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} :=
      _root_.SandwichedRenyiRelativeEntropy.convex_nonneg_cone.integral_mem _root_.SandwichedRenyiRelativeEntropy.isClosed_nonneg_cone hgσ_mem hgσ_int
    -- The pd integral points `Pρ = ∫gρ`, `Pσ = ∫gσ`, and the optimizer `H*`.
    set Pρ : L (𝒦 ⊗[ℂ] ℋ_env) :=
      TensorProduct.map (TrRight Xρ) ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) with hPρ_def
    set Pσ : L (𝒦 ⊗[ℂ] ℋ_env) :=
      TensorProduct.map (TrRight Xσ) ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) with hPσ_def
    have hτmax_pd : ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) ∈ pdSetLM (ℋ := ℋ_env) :=
      maxmixed_pdSetLM ℋ_env
    have hPρ_pd : Pρ ∈ pdSetLM (ℋ := 𝒦 ⊗[ℂ] ℋ_env) := by
      rw [hPρ_def]; exact tensorMap_pdSetLM (by rw [hXρ_def]; exact _hEρ) hτmax_pd
    have hPσ_pd : Pσ ∈ pdSetLM (ℋ := 𝒦 ⊗[ℂ] ℋ_env) := by
      rw [hPσ_def]; exact tensorMap_pdSetLM (by rw [hXσ_def]; exact _hEσ) hτmax_pd
    set Hopt := quasiVarOpt α Pρ Pσ with hHopt_def
    have hHopt_pd : Hopt ∈ pdSetLM (ℋ := 𝒦 ⊗[ℂ] ℋ_env) :=
      quasiVarOpt_pdSetLM hα0 hα_ne1 hPρ_pd hPσ_pd
    have hHopt_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Hopt := nonneg_of_pdSetLM hHopt_pd
    have hHopt_pos : Hopt.IsPositive := (LinearMap.nonneg_iff_isPositive _).mp hHopt_nn
    -- Attainment at the pd point: `Re Q_α(Pρ,Pσ) = Re quasiVar(Pρ,Pσ,H*)`.
    have hatt : (sandwichedQuasi α Pρ Pσ).re = (quasiVar α Pρ Pσ Hopt).re := by
      rw [hHopt_def, quasiVarOpt_eq_quasi_gt hα_gt hPρ_pd hPσ_pd]
    -- Integrability of `u ↦ Re quasiVar(gρu,gσu,H*)` (continuity + compact support).
    have hgρ_cont : Continuous gρ := continuous_unitaryConj_tensor_right Xρ
    have hgσ_cont : Continuous gσ := continuous_unitaryConj_tensor_right Xσ
    have hquasi_cont : Continuous (fun u => (quasiVar α (gρ u) (gσ u) Hopt).re) := by
      have h : Continuous (fun u => Function.uncurry
          (fun ρ σ => (quasiVar α ρ σ Hopt).re) (gρ u, gσ u)) :=
        (_root_.SandwichedRenyiRelativeEntropy.quasiVar_re_continuousOn_nonneg hα_gt hHopt_nn).comp_continuous
          (hgρ_cont.prodMk hgσ_cont) (fun u => Set.mk_mem_prod (hgρ_nn_all u) (hgσ_nn_all u))
      simpa only [Function.uncurry_apply_pair] using h
    have hquasi_int :
        Integrable (fun u => (quasiVar α (gρ u) (gσ u) Hopt).re) (haarUnitary ℋ_env) :=
      hquasi_cont.integrable_of_hasCompactSupport
        (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))
    -- Jensen for the (convex, continuous) `quasiVar(·,·,H*)` on the psd cone.
    have hJ := jointly_convex_integral_le (μ := haarUnitary ℋ_env)
      _root_.SandwichedRenyiRelativeEntropy.convex_nonneg_cone _root_.SandwichedRenyiRelativeEntropy.convex_nonneg_cone _root_.SandwichedRenyiRelativeEntropy.isClosed_nonneg_cone _root_.SandwichedRenyiRelativeEntropy.isClosed_nonneg_cone
      (_root_.SandwichedRenyiRelativeEntropy.quasiVar_re_jointlyConvex_nonneg hα_gt hHopt_pd)
      (_root_.SandwichedRenyiRelativeEntropy.quasiVar_re_continuousOn_nonneg hα_gt hHopt_nn)
      hgρ_mem hgσ_mem hgρ_int hgσ_int hquasi_int hmem_ρ hmem_σ
    rw [hint_ρ, hint_σ] at hJ
    -- Pointwise `quasiVar(gρu,gσu,H*) ≤ Q_α(gρu,gσu)` via the isometry `Vu = (1⊗u)∘V`.
    have hpoint : ∀ u : unitary (L ℋ_env),
        (quasiVar α (gρ u) (gσ u) Hopt).re ≤ (sandwichedQuasi α (gρ u) (gσ u)).re := by
      intro u
      set W : L (𝒦 ⊗[ℂ] ℋ_env) := TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env))
        with hW_def
      have hW_unit : W ∈ unitary (L (𝒦 ⊗[ℂ] ℋ_env)) := _root_.SandwichedRenyiRelativeEntropy.tensorMap_right_unitary_of_unitary u
      have hadjW : LinearMap.adjoint W =
          TensorProduct.map (LinearMap.id (M := 𝒦)) (star (u : L ℋ_env)) := by
        rw [hW_def, ← LinearMap.star_eq_adjoint, _root_.SandwichedRenyiRelativeEntropy.tensorMap_right_star]
      set Vu : ℋ →ₗ[ℂ] (𝒦 ⊗[ℂ] ℋ_env) := W.comp V with hVu_def
      have hVu_iso : (LinearMap.adjoint Vu).comp Vu = 1 := by
        have hWadjW : LinearMap.adjoint W * W = 1 := by
          have h := (Unitary.mem_iff.mp hW_unit).1
          rwa [LinearMap.star_eq_adjoint] at h
        rw [hVu_def, LinearMap.adjoint_comp]
        calc ((LinearMap.adjoint V).comp (LinearMap.adjoint W)).comp (W.comp V)
            = (LinearMap.adjoint V).comp ((LinearMap.adjoint W * W).comp V) := by
              simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]
          _ = (LinearMap.adjoint V).comp V := by
              rw [hWadjW, Module.End.one_eq_id, LinearMap.id_comp]
          _ = 1 := _hV
      have hgρu_eq : gρ u = (Vu.comp ρ).comp (LinearMap.adjoint Vu) := by
        simp only [hgρ_def]
        rw [hVu_def, hXρ_def, LinearMap.adjoint_comp, ← hW_def, ← hadjW]
        simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]
      have hgσu_eq : gσ u = (Vu.comp σ).comp (LinearMap.adjoint Vu) := by
        simp only [hgσ_def]
        rw [hVu_def, hXσ_def, LinearMap.adjoint_comp, ← hW_def, ← hadjW]
        simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]
      rw [hgρu_eq, hgσu_eq, _root_.SandwichedRenyiRelativeEntropy.quasiVar_isometric_conj Vu hVu_iso hα0 hα_ne1 hσ_nn hHopt_nn,
        _root_.SandwichedRenyiRelativeEntropy.sandwichedQuasi_isometric_conj Vu hVu_iso hα0 hα_ne1 hρ_nn hσ_nn]
      exact (RCLike.le_iff_re_im.mp (quasiVar_le_quasi hα_gt
        ((LinearMap.nonneg_iff_isPositive ρ).mp hρ_nn)
        ((LinearMap.nonneg_iff_isPositive σ).mp hσ_nn)
        (hHopt_pos.adjoint_conj Vu) (isUnit_of_pdSetLM _hσ))).1
    -- Combine: `Re Q_α(Pρ,Pσ) ≤ ∫ Re quasiVar ≤ ∫ Re Q_α = Re Q_α(Xρ,Xσ)`.
    have hint_le : (∫ u, (quasiVar α (gρ u) (gσ u) Hopt).re ∂(haarUnitary ℋ_env)) ≤
        (sandwichedQuasi α Xρ Xσ).re := by
      calc (∫ u, (quasiVar α (gρ u) (gσ u) Hopt).re ∂(haarUnitary ℋ_env))
          ≤ ∫ u, (sandwichedQuasi α (gρ u) (gσ u)).re ∂(haarUnitary ℋ_env) :=
            integral_mono hquasi_int hfg_int hpoint
        _ = (sandwichedQuasi α Xρ Xσ).re := h_lhs_int
    have hfinal : (sandwichedQuasi α Pρ Pσ).re ≤ (sandwichedQuasi α Xρ Xσ).re := by
      rw [hatt]; exact le_trans hJ hint_le
    have hα1_pos : (0 : ℝ) < α - 1 := by linarith
    nlinarith [hfinal, hα1_pos]

end JensenHaarCore

/-! ### The abstract Jensen-Haar interface -/

/-- **Jensen–Haar inequality (Form A, isometric Stinespring).**

    Given the data of an *isometric* Stinespring dilation — an environment
    Hilbert space `ℋ_env` and an isometry `V : ℋ →ₗ[ℂ] (ℋ ⊗ ℋ_env)` with
    `V*V = I_ℋ` — let `E γ := TrRight (V γ V*)`. Then for any
    `α ∈ [1/2, 1) ∪ (1, ∞)` and any positive-definite `ρ, σ` with
    positive-definite images `E ρ`, `E σ`,

    `(Re sandwichedQuasi α (E ρ) (E σ) − Re sandwichedQuasi α ρ σ) · (α − 1) ≤ 0`.

    This is the data-processing inequality at the `Q_α`-functional level,
    in the form directly compatible with `CPTP.exists_stinespring_dilation`
    (Form A). The previous interface — taking a unitary `U` and a
    positive-definite density matrix `τ_env` on the environment — has been
    retired together with the Naimark dilation it relied on.

    **Proof outline (Frank–Lieb arXiv:1306.5358).**
    Apply the right-twirl identity to write
      `(E γ) ⊗ τ_max = ∫ (1 ⊗ u) (V γ V*) (1 ⊗ u*) du`
    over the Haar measure on `unitary (L ℋ_env)`. Combine with tensor
    multiplicativity of `sandwichedQuasi` (and the self-identity
    `sandwichedQuasi α τ_max τ_max = Tr τ_max`) to reduce the goal to
    the inner Jensen-style inequality `jensen_haar_core`. The latter is
    proved via Lieb (`α > 1`) or Ando (`α ∈ [1/2, 1)`) joint
    convexity / concavity of `sandwichedQuasi.re`, with rank-deficiency
    handled by the convention `Q_α(ρ, σ) = ∞ when ker σ ⊄ ker ρ`. -/
theorem sandwichedQuasi_jensen_haar
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {ℋ_env : Type u} [Qudit ℋ_env] [Nontrivial ℋ_env]
    {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ))
    (V : ℋ →ₗ[ℂ] (𝒦 ⊗[ℂ] ℋ_env))
    (hV : (LinearMap.adjoint V).comp V = (1 : L ℋ))
    (hEρ : TrRight ((V.comp ρ).comp (LinearMap.adjoint V)) ∈ pdSetLM (ℋ := 𝒦))
    (hEσ : TrRight ((V.comp σ).comp (LinearMap.adjoint V)) ∈ pdSetLM (ℋ := 𝒦)) :
    ((sandwichedQuasi α
        (TrRight ((V.comp ρ).comp (LinearMap.adjoint V)))
        (TrRight ((V.comp σ).comp (LinearMap.adjoint V)))).re -
      (sandwichedQuasi α ρ σ).re) * (α - 1) ≤ 0 := by
  -- Reduce `sandwichedQuasi_jensen_haar` to `jensen_haar_core` plus the
  -- two helper lemmas (tensor mult collapse + isometric invariance).
  have hα0 : 0 < α := by linarith
  have hα_ne0 : α ≠ 0 := ne_of_gt hα0
  set Eρ : L 𝒦 := TrRight ((V.comp ρ).comp (LinearMap.adjoint V)) with hEρ_def
  set Eσ : L 𝒦 := TrRight ((V.comp σ).comp (LinearMap.adjoint V)) with hEσ_def
  set τ_max : L ℋ_env := (Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env) with hτ_max_def
  -- `τ_max ∈ pdSetLM` and `Tr τ_max = 1`.
  have hτ_max_pd : τ_max ∈ pdSetLM (ℋ := ℋ_env) := maxmixed_pdSetLM ℋ_env
  have hτ_max_trace : Tr τ_max = 1 := by
    rw [hτ_max_def, map_smul, smul_eq_mul, LinearMap.trace_one]
    have hd : (Module.finrank ℂ ℋ_env : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℂ) (M := ℋ_env)).ne'
    field_simp
  -- LHS factorisation: `Q_α(Eρ ⊗ τ_max, Eσ ⊗ τ_max) = Q_α(Eρ, Eσ)`.
  have hLHS_factor : sandwichedQuasi α
      (TensorProduct.map Eρ τ_max : L (𝒦 ⊗[ℂ] ℋ_env))
      (TensorProduct.map Eσ τ_max) =
      sandwichedQuasi α Eρ Eσ := by
    rw [sandwichedQuasi_tensor α Eρ Eσ τ_max τ_max
        (nonneg_of_pdSetLM hEρ) (nonneg_of_pdSetLM hEσ)
        (nonneg_of_pdSetLM hτ_max_pd) (nonneg_of_pdSetLM hτ_max_pd),
        sandwichedQuasi_self_pdSetLM hα_ne0 hτ_max_pd, hτ_max_trace, mul_one]
  -- RHS factorisation (isometric invariance):
  -- `Q_α(V ρ V*, V σ V*) = Q_α(ρ, σ)`, valid for all `α > 0`, `α ≠ 1`.
  -- (In finite dimensions there is no CFC convention obstruction even for `α > 1`;
  -- see `sandwichedQuasi_isometric_conj`.)
  have hRHS_factor : sandwichedQuasi α
      ((V.comp ρ).comp (LinearMap.adjoint V))
      ((V.comp σ).comp (LinearMap.adjoint V)) =
      sandwichedQuasi α ρ σ :=
    _root_.SandwichedRenyiRelativeEntropy.sandwichedQuasi_isometric_conj V hV hα0 hα_ne1
      (nonneg_of_pdSetLM hρ) (nonneg_of_pdSetLM hσ)
  -- Apply the inner Jensen-Haar (`jensen_haar_core`) and substitute.
  have h_core := _root_.SandwichedRenyiRelativeEntropy.jensen_haar_core hα_ge hα_ne1 hρ hσ V hV hEρ hEσ
  change ((sandwichedQuasi α Eρ Eσ).re - (sandwichedQuasi α ρ σ).re) * (α - 1) ≤ 0
  have hLHS_re : (sandwichedQuasi α
      (TensorProduct.map Eρ τ_max : L (𝒦 ⊗[ℂ] ℋ_env))
      (TensorProduct.map Eσ τ_max)).re = (sandwichedQuasi α Eρ Eσ).re := by
    rw [hLHS_factor]
  have hRHS_re : (sandwichedQuasi α
      ((V.comp ρ).comp (LinearMap.adjoint V))
      ((V.comp σ).comp (LinearMap.adjoint V))).re =
      (sandwichedQuasi α ρ σ).re := by
    rw [hRHS_factor]
  rw [← hLHS_re, ← hRHS_re]; exact h_core
end SandwichedRenyiRelativeEntropy


