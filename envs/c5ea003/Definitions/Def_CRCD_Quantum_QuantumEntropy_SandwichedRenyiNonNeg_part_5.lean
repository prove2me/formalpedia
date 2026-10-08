-- Prove2me | Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiNonNeg_part_5
-- name    : CRCD_Quantum_QuantumEntropy_SandwichedRenyiNonNeg_part_5
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T01:44:30.79048+00:00
-- url     : https://prove2.me/theorems/3068e8d2-6e7e-4245-ac67-f991f8ec217d
-- title:
--   Extended-real data processing for support-aware sandwiched Rényi divergence
-- statement:
--   Let $\Phi:L(H)\to L(K)$ be CPTP between nonzero finite-dimensional complex Hilbert spaces. For every $\alpha\ge1/2$, $\alpha\ne1$ and positive semidefinite $\rho,\sigma$, the part proves
--   $$
--   D^{\mathrm{NN}}_\alpha(\Phi(\rho)\Vert\Phi(\sigma))
--   \le D^{\mathrm{NN}}_\alpha(\rho\Vert\sigma).
--   $$
--   Here $D^{\mathrm{NN}}_\alpha$ is the preceding trace-normalized EReal divergence: its finite branch uses natural logarithms, its above-one support-mismatch branch is $+\infty$, and its below-one branch is $+\infty$ when $\rho\ne0$ and the quasi-entropy vanishes. The assertion permits zero inputs, singular inputs, and infinite divergence. It requires no faithfulness, support inclusion, nonvanishing quasi-entropy, or unit-trace premise. The separate supporting fact states that $\Phi(\rho)\ne0$ whenever $\rho\ge0$ and $\rho\ne0$, by trace preservation. These are natural-logarithmic state-operator results; bit conversion and nonnegative truncation are not performed here.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumEntropy/SandwichedRenyiNonNeg.lean#L2288-L2516

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
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiNonNeg_part_4
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
# Sandwiched Rényi divergence on non-negative operators (Frank–Lieb extension)

This file extends the sandwiched Rényi divergence `D_α(ρ ‖ σ)` from the
positive-definite case to **non-negative** `ρ, σ ≥ 0`, following the convention
of Frank–Lieb (arXiv:1306.5358v3, §I.A).

## Main definitions

* `suppLE ρ σ` — support condition `ker σ ≤ ker ρ` (equivalent to `supp ρ ⊂ supp σ`).
* `sandwichedRenyiDivNN α ρ σ` — Frank–Lieb extension on `EReal`: equals
  `sandwichedRenyiDiv α ρ σ` when `α < 1` or `suppLE ρ σ`, and `⊤ : EReal`
  when `α > 1` and `¬ suppLE ρ σ`.

## Main theorem

* `sandwichedRenyiDivNN_monotone` — **Theorem 1** (Frank–Lieb): for any CPTP map
  `E : CPTP ℋ ℋ`, any `α ∈ [1/2, 1) ∪ (1, ∞)`, and any non-negative `ρ, σ`,
  `D_α^{NN}(E ρ ‖ E σ) ≤ D_α^{NN}(ρ ‖ σ)`.

## Proof structure

The main theorem reduces via case analysis:

* `α > 1`, `¬ suppLE ρ σ`: RHS is `⊤`, trivial.
* otherwise: real-valued inequality, proven via the faithful-approximation
  `F_λ := (1−λ) E + λ · depolarizing` (faithful for `λ > 0`), the perturbed
  Theorem 1 for faithful channels (`sandwichedRenyiDiv_monotone_nonneg_perturbed`),
  and boundary continuity of `sandwichedRenyiDiv` as `ε → 0+`.
-/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel MeasureTheory TensorProduct
open scoped ComplexOrder NNReal Topology

universe u

set_option linter.style.longLine false

/-! ### Support condition `suppLE` -/





/-! ### Frank–Lieb explicit formula -/



/-! ### Auxiliary spectral / order lemmas -/









/-! ### Support preservation under positive maps -/



/-! ### Outer-product helpers and the depolarizing-channel Kraus decomposition -/











/-! ### Faithful approximating channel `F_λ := (1−λ) E + λ · depolarizing` -/

















/-! ### Continuity of `CFC.rpow` and `sandwichedQuasi` on the full non-negative cone

For a **non-negative exponent** `p ≥ 0` the map `x ↦ x^p` is continuous on all of
`ℝ≥0` (no pseudo-inverse discontinuity at `0`), so `A ↦ CFC.rpow A p` is continuous
on the whole non-negative cone `{A | 0 ≤ A}`, not just on the strictly-positive
`pdSetLM`. This is the analytic engine for the `α < 1` boundary continuity, where the
exponents `β = (1−α)/(2α) > 0` and `α > 0` are both non-negative. -/















/-! ### Boundary continuity of `sandwichedRenyiDiv` along the perturbation path -/

/-! #### Eigenvector formulas for the continuous functional calculus -/





























/-! ### Helpers for the `α < 1` main-theorem case -/











/-! ### Real-valued monotonicity (used in the main theorem) -/















/-! ### Main theorem: Theorem 1 for non-negative operators, general CPTP -/

/-- **Theorem 1 (Frank–Lieb, arXiv:1306.5358v3): Data-processing for the
    sandwiched Rényi relative entropy on non-negative operators.**

    For any CPTP map `E : CPTP ℋ ℋ`, any `α ∈ [1/2, 1) ∪ (1, ∞)`, and any
    non-negative `ρ, σ : L ℋ`,

      `D_α^{NN}(E ρ ‖ E σ) ≤ D_α^{NN}(ρ ‖ σ)`,

    where `D_α^{NN}` is the Frank–Lieb extension (`sandwichedRenyiDivNN`) with
    value `+∞ : EReal` on the support-mismatch region for `α > 1`. -/
theorem sandwichedRenyiDivNN_monotone
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ}
    (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    sandwichedRenyiDivNN α (E.toFun ρ) (E.toFun σ) ≤
      sandwichedRenyiDivNN α ρ σ := by
  have hEρ : (0 : L 𝒦) ≤ E.toFun ρ := map_nonneg E.toCompletelyPositiveMap hρ
  have hEσ : (0 : L 𝒦) ≤ E.toFun σ := map_nonneg E.toCompletelyPositiveMap hσ
  by_cases hα_gt : 1 < α
  · -- `α > 1`.
    by_cases hsupp : suppLE ρ σ
    · have hEsupp : suppLE (E.toFun ρ) (E.toFun σ) := suppLE_of_CPTP E hρ hσ hsupp
      by_cases hρ0 : ρ = 0
      · -- `ρ = 0`: both divergences are `0`.
        have hEρ0 : E.toFun ρ = 0 := by
          rw [hρ0]; exact map_zero E.toCompletelyPositiveMap.toLinearMap
        have h_LHS0 : sandwichedRenyiDivNN α (E.toFun ρ) (E.toFun σ) = ((0 : ℝ) : EReal) := by
          rw [hEρ0]
          unfold sandwichedRenyiDivNN
          rw [if_neg, _root_.SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv_zero_left]
          rintro (⟨_, h⟩ | ⟨h, _⟩)
          · exact h (le_top.trans_eq (LinearMap.ker_zero).symm)
          · linarith
        have h_RHS0 : sandwichedRenyiDivNN α ρ σ = ((0 : ℝ) : EReal) := by
          rw [hρ0]
          unfold sandwichedRenyiDivNN
          rw [if_neg, _root_.SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv_zero_left]
          rintro (⟨_, h⟩ | ⟨h, _⟩)
          · exact h (le_top.trans_eq (LinearMap.ker_zero).symm)
          · linarith
        rw [h_LHS0, h_RHS0]
      · have h_LHS : sandwichedRenyiDivNN α (E.toFun ρ) (E.toFun σ) =
            ((sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) : ℝ) : EReal) := by
          unfold sandwichedRenyiDivNN
          rw [if_neg]; rintro (⟨_, h⟩ | ⟨h, _⟩)
          · exact h hEsupp
          · linarith
        have h_RHS : sandwichedRenyiDivNN α ρ σ =
            ((sandwichedRenyiDiv α ρ σ : ℝ) : EReal) := by
          unfold sandwichedRenyiDivNN
          rw [if_neg]; rintro (⟨_, h⟩ | ⟨h, _⟩)
          · exact h hsupp
          · linarith
        rw [h_LHS, h_RHS]
        have h_real : sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) ≤
            sandwichedRenyiDiv α ρ σ :=
          _root_.SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN_monotone_real_aux E hα_gt hρ hσ hsupp hEsupp hρ0
        exact_mod_cast h_real
    · have h_RHS_top : sandwichedRenyiDivNN α ρ σ = (⊤ : EReal) := by
        unfold sandwichedRenyiDivNN
        exact if_pos (Or.inl ⟨hα_gt, hsupp⟩)
      rw [h_RHS_top]
      exact le_top
  · -- `α < 1`.
    push_neg at hα_gt
    have hα_lt : α < 1 := lt_of_le_of_ne hα_gt hα_ne1
    have hα0 : 0 < α := by linarith
    by_cases hRtop : ρ ≠ 0 ∧ (sandwichedQuasi α ρ σ).re = 0
    · -- Orthogonal supports (`Q_α = 0`, `ρ ≠ 0`): RHS is `⊤`.
      have h_RHS_top : sandwichedRenyiDivNN α ρ σ = (⊤ : EReal) := by
        unfold sandwichedRenyiDivNN
        exact if_pos (Or.inr ⟨hα_lt, hRtop.1, hRtop.2⟩)
      rw [h_RHS_top]
      exact le_top
    · by_cases hρ0 : ρ = 0
      · -- `ρ = 0`: both divergences are `0`.
        have hEρ0 : E.toFun ρ = 0 := by rw [hρ0]; exact map_zero E.toCompletelyPositiveMap.toLinearMap
        have h_LHS0 : sandwichedRenyiDivNN α (E.toFun ρ) (E.toFun σ) = ((0 : ℝ) : EReal) := by
          rw [hEρ0]
          unfold sandwichedRenyiDivNN
          rw [if_neg, _root_.SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv_zero_left]
          rintro (⟨h, _⟩ | ⟨_, h, _⟩)
          · linarith
          · exact h rfl
        have h_RHS0 : sandwichedRenyiDivNN α ρ σ = ((0 : ℝ) : EReal) := by
          rw [hρ0]
          unfold sandwichedRenyiDivNN
          rw [if_neg, _root_.SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv_zero_left]
          rintro (⟨h, _⟩ | ⟨_, h, _⟩)
          · linarith
          · exact h rfl
        rw [h_LHS0, h_RHS0]
      · -- `ρ ≠ 0` and `Q_α(ρ‖σ) ≠ 0`: real-valued DPI applies (LHS also finite by reflection).
        have hQρσ : (sandwichedQuasi α ρ σ).re ≠ 0 := fun h => hRtop ⟨hρ0, h⟩
        have hQEρσ : (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re ≠ 0 :=
          _root_.SandwichedRenyiRelativeEntropy.sandwichedQuasi_re_ne_zero_of_CPTP E hα_ge hα_lt hρ hσ hρ0 hQρσ
        have h_LHS : sandwichedRenyiDivNN α (E.toFun ρ) (E.toFun σ) =
            ((sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) : ℝ) : EReal) := by
          unfold sandwichedRenyiDivNN
          rw [if_neg]; rintro (⟨h, _⟩ | ⟨_, _, h⟩)
          · linarith
          · exact hQEρσ h
        have h_RHS : sandwichedRenyiDivNN α ρ σ =
            ((sandwichedRenyiDiv α ρ σ : ℝ) : EReal) := by
          unfold sandwichedRenyiDivNN
          rw [if_neg]; rintro (⟨h, _⟩ | ⟨_, _, h⟩)
          · linarith
          · exact hQρσ h
        rw [h_LHS, h_RHS]
        have h_real : sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) ≤
            sandwichedRenyiDiv α ρ σ :=
          _root_.SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN_monotone_real_aux_lt E hα_ge hα_lt hρ hσ hρ0 hQρσ hQEρσ
        exact_mod_cast h_real

/-! ### α = ∞ : max-relative entropy -/

section MaxRelEntropy

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]



















/-- `E ρ ≠ 0` for non-negative `ρ ≠ 0` and a CPTP map `E` (trace is preserved). -/
lemma CPTP_toFun_ne_zero
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] (E : CPTP ℋ 𝒦)
    {ρ : L ℋ} (hρ : 0 ≤ ρ) (hρ0 : ρ ≠ 0) :
    E.toFun ρ ≠ 0 := by
  intro h
  have htr : (Tr ρ).re = 0 := by rw [E.trace_map ρ, h]; simp
  exact absurd htr (ne_of_gt (trace_re_pos_of_ne_zero hρ hρ0))
end MaxRelEntropy
end SandwichedRenyiRelativeEntropy


