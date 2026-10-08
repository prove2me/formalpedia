-- Prove2me | Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedQuasiJensen_part_3
-- name    : CRCD_Quantum_QuantumEntropy_SandwichedQuasiJensen_part_3
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T01:22:47.30935+00:00
-- url     : https://prove2.me/theorems/14f12cc6-05a3-46f3-a8ce-39ca1029afd3
-- title:
--   Faithful and perturbed data processing for trace-normalized Rényi divergence
-- statement:
--   Let $\Phi:L(H)\to L(K)$ be CPTP on nonzero finite-dimensional complex Hilbert spaces, and let $\alpha\ge1/2$, $\alpha\ne1$. For positive-definite $\rho,\sigma$ with positive-definite images, the trace-normalized real divergence satisfies
--   $$
--   D_\alpha(\Phi(\rho)\Vert\Phi(\sigma))\le D_\alpha(\rho\Vert\sigma),\qquad
--   D_\alpha(\rho\Vert\sigma)=\frac{\ln(\operatorname{Re}Q_\alpha(\rho\Vert\sigma)/\operatorname{Re}\operatorname{Tr}\rho)}{\alpha-1}.
--   $$
--   This uses natural logarithms and arbitrary positive traces, rather than requiring density operators or converting to bits.
--
--   For $\rho,\sigma\ge0$, the part also proves the perturbed inequality
--   $$
--   D_\alpha(\Phi(\rho+\varepsilon I_H)\Vert\Phi(\sigma+\varepsilon I_H))
--   \le D_\alpha(\rho+\varepsilon I_H\Vert\sigma+\varepsilon I_H)
--   $$
--   for every $\varepsilon>0$, under the additional faithfulness premise $\Phi(I_H)>0$. Both zero and singular unperturbed inputs are permitted in this version. Finally, a positive real scalar multiple of a positive-definite operator is positive definite. No support-aware infinity extension is introduced in this part.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumEntropy/SandwichedQuasiJensen.lean#L1406-L1619

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
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedQuasiJensen_part_2
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

/-- Monotonicity of the sandwiched Rényi divergence under CPTP maps (data-processing inequality).

    For any quantum channel `E : CPTP ℋ ℋ`, any `α ∈ [1/2, 1) ∪ (1, ∞)`, and any
    positive-definite operators `ρ, σ` with positive-definite images `E ρ`, `E σ`,
        `D_α(E ρ ‖ E σ) ≤ D_α(ρ ‖ σ)`.

    **Proof.** Apply the isometric Stinespring dilation
    `E(γ) = TrRight (V γ V*)` (`CPTP.exists_stinespring_dilation`, Form A).
    The central inequality
        `(Re sandwichedQuasi α (Eρ) (Eσ) − Re sandwichedQuasi α ρ σ) · (α − 1) ≤ 0`
    follows from `sandwichedQuasi_jensen_haar` (the abstract Jensen–Haar
    inequality above). Dividing by `Tr Eρ = Tr ρ > 0` (trace preservation
    by `E`) and applying `(α−1)⁻¹ log(·)` gives the result, with sign
    tracking unifying the `α > 1` and `α < 1` cases. -/
theorem sandwichedRenyiDiv_monotone
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ}
    (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ))
    (hEρ : E.toFun ρ ∈ pdSetLM (ℋ := 𝒦))
    (hEσ : E.toFun σ ∈ pdSetLM (ℋ := 𝒦)) :
    sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) ≤ sandwichedRenyiDiv α ρ σ := by
  have hα0 : 0 < α := by linarith
  have hα_ne0 : α ≠ 0 := ne_of_gt hα0
  -- Step 1: Isometric Stinespring dilation (Form A).
  obtain ⟨ℋ_env, h_qudit, h_nontriv, V, hV_iso, hV_eq⟩ :=
    CPTP.exists_stinespring_dilation E
  letI := h_qudit
  letI := h_nontriv
  -- Step 2: Eρ and Eσ as the (isometric) Stinespring images.
  have hEρ_eq : E.toFun ρ = TrRight ((V.comp ρ).comp (LinearMap.adjoint V)) := hV_eq ρ
  have hEσ_eq : E.toFun σ = TrRight ((V.comp σ).comp (LinearMap.adjoint V)) := hV_eq σ
  -- pdSetLM membership of the Stinespring images (re-stated in the form needed
  -- by `sandwichedQuasi_jensen_haar`).
  have hEρ' : TrRight ((V.comp ρ).comp (LinearMap.adjoint V)) ∈ pdSetLM (ℋ := 𝒦) :=
    hEρ_eq ▸ hEρ
  have hEσ' : TrRight ((V.comp σ).comp (LinearMap.adjoint V)) ∈ pdSetLM (ℋ := 𝒦) :=
    hEσ_eq ▸ hEσ
  -- Step 3: the central Q_α-inequality, from `sandwichedQuasi_jensen_haar`.
  have hQ_ineq :
      ((sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re - (sandwichedQuasi α ρ σ).re) *
        (α - 1) ≤ 0 := by
    have h := sandwichedQuasi_jensen_haar hα_ge hα_ne1 hρ hσ V hV_iso hEρ' hEσ'
    rw [hEρ_eq, hEσ_eq]
    exact h
  -- Step 4: unfold D_α and apply log monotonicity.
  unfold sandwichedRenyiDiv
  -- `E` preserves traces: `Tr (E.toFun ρ) = Tr ρ`.
  have hTr_Eρ : (Tr (E.toFun ρ)).re = (Tr ρ).re := by
    rw [← E.trace_map ρ]
  -- Positivity of the relevant real parts.
  have hTr_ρ_pos : (0 : ℝ) < (Tr ρ).re := trace_re_pos_of_pdSetLM hρ
  -- Positivity of `Re sandwichedQuasi α ρ' σ'` for `ρ', σ' ∈ pdSetLM`: the inner
  -- operator `σ'^β ρ' σ'^β` is pd, hence `(·)^α` is pd, hence the trace is positive.
  have hQ_pos_aux : ∀ {𝒥 : Type u} [Qudit 𝒥] [Nontrivial 𝒥] {ρ' σ' : L 𝒥},
      ρ' ∈ pdSetLM (ℋ := 𝒥) → σ' ∈ pdSetLM (ℋ := 𝒥) →
      (0 : ℝ) < (sandwichedQuasi α ρ' σ').re := by
    intro 𝒥 _ _ ρ' σ' hρ' hσ'
    unfold sandwichedQuasi
    have hP_pd : CFC.rpow σ' ((1 - α) / (2 * α)) ∈ pdSetLM (ℋ := 𝒥) := pdSetLM_rpow_ne hσ'
    have hP_sa : IsSelfAdjoint (CFC.rpow σ' ((1 - α) / (2 * α))) :=
      IsSelfAdjoint.of_nonneg (nonneg_of_pdSetLM hP_pd)
    have hP_unit : IsUnit (CFC.rpow σ' ((1 - α) / (2 * α))) := isUnit_of_pdSetLM hP_pd
    have h_inner_eq :
        CFC.rpow σ' ((1 - α) / (2 * α)) * ρ' * CFC.rpow σ' ((1 - α) / (2 * α)) =
        star (CFC.rpow σ' ((1 - α) / (2 * α))) * ρ' * CFC.rpow σ' ((1 - α) / (2 * α)) := by
      rw [hP_sa.star_eq]
    have h_inner_pd :
        (CFC.rpow σ' ((1 - α) / (2 * α)) * ρ' * CFC.rpow σ' ((1 - α) / (2 * α))) ∈
          pdSetLM (ℋ := 𝒥) := by
      rw [h_inner_eq]; exact pdSetLM_conj hρ' hP_unit
    have h_pow_pd :
        CFC.rpow
            (CFC.rpow σ' ((1 - α) / (2 * α)) * ρ' * CFC.rpow σ' ((1 - α) / (2 * α))) α ∈
          pdSetLM (ℋ := 𝒥) := pdSetLM_rpow_ne h_inner_pd
    exact trace_re_pos_of_pdSetLM h_pow_pd
  have hQρσ_pos : (0 : ℝ) < (sandwichedQuasi α ρ σ).re := hQ_pos_aux hρ hσ
  have hQEρEσ_pos : (0 : ℝ) < (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re :=
    hQ_pos_aux hEρ hEσ
  -- Final step: deduce the log inequality.
  -- From `hQ_ineq`: `(Q_α(Eρ,Eσ).re − Q_α(ρ,σ).re) · (α-1) ≤ 0`.
  rcases lt_or_gt_of_ne hα_ne1 with hα_lt | hα_gt
  · -- α < 1: α - 1 < 0
    have hα1_neg : (α - 1 : ℝ) < 0 := by linarith
    have hQ_ge :
        (sandwichedQuasi α ρ σ).re ≤ (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re := by
      nlinarith
    have hlog : Real.log ((sandwichedQuasi α ρ σ).re / (Tr ρ).re) ≤
        Real.log ((sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re /
          (Tr (E.toFun ρ)).re) := by
      rw [hTr_Eρ]
      exact Real.log_le_log (div_pos hQρσ_pos hTr_ρ_pos)
        (div_le_div_of_nonneg_right hQ_ge (le_of_lt hTr_ρ_pos))
    have h1α : (1 / (α - 1) : ℝ) < 0 := by
      rw [one_div]; exact inv_neg''.mpr hα1_neg
    nlinarith
  · -- α > 1: α - 1 > 0
    have hα1_pos : (0 : ℝ) < α - 1 := by linarith
    have hQ_le' :
        (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re ≤ (sandwichedQuasi α ρ σ).re := by
      nlinarith
    have hlog : Real.log ((sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re /
        (Tr (E.toFun ρ)).re) ≤
          Real.log ((sandwichedQuasi α ρ σ).re / (Tr ρ).re) := by
      rw [hTr_Eρ]
      exact Real.log_le_log (div_pos hQEρEσ_pos hTr_ρ_pos)
        (div_le_div_of_nonneg_right hQ_le' (le_of_lt hTr_ρ_pos))
    have h1α_pos : (0 : ℝ) < 1 / (α - 1) := by
      rw [one_div]; exact inv_pos.mpr hα1_pos
    exact mul_le_mul_of_nonneg_left hlog (le_of_lt h1α_pos)

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

/-- A positive real scalar multiple of a pd operator is pd. -/
lemma pdSetLM_pos_smul
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) {c : ℝ} (hc : 0 < c) :
    ((c : ℂ) • A) ∈ pdSetLM (ℋ := ℋ) := by
  obtain ⟨εA, hεA_pos, hεA_le⟩ := _root_.SandwichedRenyiRelativeEntropy.pdSetLM_exists_pos_lower_bound hA
  obtain ⟨MA, hMA_le⟩ := _root_.SandwichedRenyiRelativeEntropy.exists_upper_bound_self_adjoint hA.1
  have h_toCLM_smul : ((c : ℂ) • A).toContinuousLinearMap =
      (c : ℂ) • A.toContinuousLinearMap := by ext x; rfl
  -- `(c : ℂ) • A.toCLM = c • A.toCLM` (using ℝ ↪ ℂ tower).
  have h_smul_eq : (c : ℂ) • A.toContinuousLinearMap =
      c • A.toContinuousLinearMap := Complex.coe_smul c _
  refine _root_.SandwichedRenyiRelativeEntropy.pdSubCone_subset_pdSetLM (ℋ := ℋ) (ε := c * εA) (mul_pos hc hεA_pos)
      (M := c * MA) ⟨?_, ?_⟩
  · rw [h_toCLM_smul, h_smul_eq]
    have h_smul_lhs : (c * εA) • (1 : LownerHeinzTheorem.L ℋ) =
        c • (εA • (1 : LownerHeinzTheorem.L ℋ)) := by rw [mul_smul]
    rw [h_smul_lhs]
    have h_nn : (0 : LownerHeinzTheorem.L ℋ) ≤
        c • A.toContinuousLinearMap - c • (εA • (1 : LownerHeinzTheorem.L ℋ)) := by
      rw [← smul_sub]
      exact smul_nonneg hc.le (sub_nonneg.mpr hεA_le)
    exact sub_nonneg.mp h_nn
  · rw [h_toCLM_smul, h_smul_eq]
    have h_smul_rhs : (c * MA) • (1 : LownerHeinzTheorem.L ℋ) =
        c • (MA • (1 : LownerHeinzTheorem.L ℋ)) := by rw [mul_smul]
    rw [h_smul_rhs]
    have h_nn : (0 : LownerHeinzTheorem.L ℋ) ≤
        c • (MA • (1 : LownerHeinzTheorem.L ℋ)) - c • A.toContinuousLinearMap := by
      rw [← smul_sub]
      exact smul_nonneg hc.le (sub_nonneg.mpr hMA_le)
    exact sub_nonneg.mp h_nn

/-- **Theorem 1, non-negative perturbed version** (Frank–Lieb, arXiv:1306.5358).

    For any quantum channel `E : CPTP ℋ ℋ` whose unital image `E 1` is
    positive-definite (i.e., `E` is *faithful*), any `α ∈ [1/2, 1) ∪ (1, ∞)`,
    any **non-negative** `ρ, σ`, and any `ε > 0`:

      `D_α(E(ρ + ε•1) ‖ E(σ + ε•1)) ≤ D_α(ρ + ε•1 ‖ σ + ε•1)`.

    This is the perturbed form of Frank–Lieb's monotonicity theorem extended
    from positive-definite to non-negative operators. The unperturbed
    inequality (i.e., `D_α(E ρ ‖ E σ) ≤ D_α(ρ ‖ σ)` for non-negative `ρ, σ`
    using the extended definition with `+∞` for divergent cases) is recovered
    as `ε → 0+` via continuity of `D_α` (finite case) or vacuously (when both
    sides diverge to `+∞`). -/
theorem sandwichedRenyiDiv_monotone_nonneg_perturbed
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ}
    (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hEI : E.toFun (1 : L ℋ) ∈ pdSetLM (ℋ := 𝒦))
    {ε : ℝ} (hε : 0 < ε) :
    sandwichedRenyiDiv α (E.toFun (ρ + (ε : ℂ) • (1 : L ℋ)))
        (E.toFun (σ + (ε : ℂ) • (1 : L ℋ))) ≤
      sandwichedRenyiDiv α (ρ + (ε : ℂ) • (1 : L ℋ)) (σ + (ε : ℂ) • (1 : L ℋ)) := by
  -- Positivity of `E` is automatic for completely-positive maps.
  have hE_pos : ∀ {X : L ℋ}, 0 ≤ X → 0 ≤ E.toFun X := fun {X} hX =>
    map_nonneg E.toCompletelyPositiveMap hX
  -- Perturbed operators are pd.
  have hρ_ε : (ρ + (ε : ℂ) • (1 : L ℋ)) ∈ pdSetLM (ℋ := ℋ) :=
    nonneg_add_pos_smul_one_pdSetLM hρ hε
  have hσ_ε : (σ + (ε : ℂ) • (1 : L ℋ)) ∈ pdSetLM (ℋ := ℋ) :=
    nonneg_add_pos_smul_one_pdSetLM hσ hε
  -- `E` is linear, so `E(ρ + ε • 1) = E ρ + ε • E 1`, and similarly for σ.
  set Elm : (L ℋ) →ₗ[ℂ] (L 𝒦) := E.toCompletelyPositiveMap.toLinearMap with hElm_def
  have hE_toFun_eq : ∀ X, E.toFun X = Elm X := fun _ => rfl
  have hE_linear : ∀ X, E.toFun (X + (ε : ℂ) • (1 : L ℋ)) =
      E.toFun X + (ε : ℂ) • E.toFun (1 : L ℋ) := by
    intro X
    rw [hE_toFun_eq, hE_toFun_eq, hE_toFun_eq, LinearMap.map_add, LinearMap.map_smul]
  -- `E(ρ + ε • 1) = E ρ + ε • E 1` is pd (non-negative + ε • pd).
  have hEρ_ε : E.toFun (ρ + (ε : ℂ) • (1 : L ℋ)) ∈ pdSetLM (ℋ := 𝒦) := by
    rw [hE_linear]
    exact pdSetLM_add_nonneg (hE_pos hρ) (pdSetLM_pos_smul hEI hε)
  have hEσ_ε : E.toFun (σ + (ε : ℂ) • (1 : L ℋ)) ∈ pdSetLM (ℋ := 𝒦) := by
    rw [hE_linear]
    exact pdSetLM_add_nonneg (hE_pos hσ) (pdSetLM_pos_smul hEI hε)
  -- Apply the pd Theorem 1.
  exact sandwichedRenyiDiv_monotone E hα_ge hα_ne1 hρ_ε hσ_ε hEρ_ε hEσ_ε
end SandwichedRenyiRelativeEntropy


