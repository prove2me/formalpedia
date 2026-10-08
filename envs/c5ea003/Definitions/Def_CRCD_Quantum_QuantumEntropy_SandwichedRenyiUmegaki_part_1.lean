-- Prove2me | Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiUmegaki_part_1
-- name    : CRCD_Quantum_QuantumEntropy_SandwichedRenyiUmegaki_part_1
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T01:56:57.112619+00:00
-- url     : https://prove2.me/theorems/2871fb37-e034-491a-ac70-b2e2237fc571
-- title:
--   Normalized Umegaki entropy, the order-one derivative, and singular perturbation limits
-- statement:
--   For operators on a finite-dimensional complex Hilbert space define the natural-logarithmic, trace-normalized real functional
--   $$
--   U(\rho\Vert\sigma)=\frac{\operatorname{Re}\operatorname{Tr}[\rho(\log\rho-\log\sigma)]}{\operatorname{Re}\operatorname{Tr}\rho},\qquad
--   U^{\mathrm{NN}}(\rho\Vert\sigma)=
--   \begin{cases}U(\rho\Vert\sigma),&\ker\sigma\subseteq\ker\rho,\\+\infty,&\text{otherwise}.\end{cases}
--   $$
--   The formal definitions use total functional calculus and division, so $U(0\Vert\sigma)=0$; they do not assume trace one. The support extension is EReal-valued and its entropy interpretation concerns positive semidefinite inputs on a nonzero space. No conversion from nats to bits is included.
--
--   For positive-definite $\rho,\sigma$, the newly proved derivative and right limit are
--   $$
--   \left.\frac{d}{d\alpha}\operatorname{Re}Q_\alpha(\rho\Vert\sigma)\right|_{\alpha=1}
--   =\operatorname{Re}\operatorname{Tr}[\rho(\log\rho-\log\sigma)],\qquad
--   \lim_{\alpha\to1^+}D_\alpha(\rho\Vert\sigma)=U(\rho\Vert\sigma).
--   $$
--   The derivative splits into an outer-power contribution $\operatorname{Re}\operatorname{Tr}(\rho\log\rho)$ and a conjugating-power contribution $-\operatorname{Re}\operatorname{Tr}(\rho\log\sigma)$. The part proves a trace-power integral identity and a general continuous-integrand averaging limit supporting this calculation. For CPTP $\Phi$ on nonzero finite-dimensional spaces, $U(\Phi(\rho)\Vert\Phi(\sigma))\le U(\rho\Vert\sigma)$ when both input and output pairs are positive definite.
--
--   For $\rho,\sigma\ge0$, $\rho\ne0$ and support inclusion, $U(\rho+\varepsilon I\Vert\sigma+\varepsilon I)\to U(\rho\Vert\sigma)$ as $\varepsilon\to0^+$. The cross-term limit $\operatorname{Re}\operatorname{Tr}[(\rho+\varepsilon I)\log(\sigma+\varepsilon I)]\to\operatorname{Re}\operatorname{Tr}(\rho\log\sigma)$ needs only $\sigma\ge0$ and the kernel inclusion, with no separate positivity premise on $\rho$. Further facts give continuity along paths of self-adjoint invertible operators with nonzero limiting first trace, the bound $U(F_\lambda(\rho)\Vert F_\lambda(\sigma))\le U(\rho\Vert\sigma)$ under the positive-input/support premises for $0<\lambda\le1$, and the scalar limits $u\ln u\to0$ and $\lambda\ln(\lambda c)\to0$ for $c>0$.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumEntropy/SandwichedRenyiUmegaki.lean#L71-L648

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
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Definitions.Def_CRCD_Quantum_QuantumEntropy_CFCDeriv
import Definitions.Def_CRCD_Quantum_QuantumEntropy_HaarUnitary
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedQuasiJensen_part_3
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiNonNeg_part_5
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
# Umegaki relative entropy as the `α → 1` limit

This file extends the Frank–Lieb data-processing programme to the boundary case
`α = 1`, where the sandwiched Rényi divergence degenerates to the **Umegaki
relative entropy**.

It is the companion of the `α = ∞` (max-relative entropy) case, proven in
`Quantum.QuantumEntropy.SandwichedRenyiNonNeg` (`maxRelEntropyNN_monotone`).

## Status

The whole `α = 1` programme (following Müller-Lennert et al., arXiv:1306.3142) is
**fully proven, sorry-free**.

* `umegakiNorm`, `umegakiRelEntropyNN` — explicit definitions.
* `hasDerivAt_sandwichedQuasi_re_one` — the derivative of
  `α ↦ Re Tr((σ^{(1-α)/2α} ρ σ^{(1-α)/2α})^α)` at `α = 1` is `Re Tr(ρ(log ρ − log σ))`.
  Assembled from `hasDerivAt_partB` (conjugating-power term) and `hasDerivAt_partA`
  (outer-power term: fixed-base FTC + averaging with the exp-based joint continuity
  `continuousAt_quasiIntegrand` — no Duhamel needed).
* `sandwichedRenyiDiv_tendsto_umegaki` — the `α → 1⁺` limit equals `umegakiNorm`.
* `umegakiNorm_monotone_pd` — DPI for positive-definite `ρ, σ`.
* `umegakiRelEntropyNN_monotone` — the general **non-negative** DPI, via the
  faithful-perturbation NN→pd reduction (`umegakiNorm_faithfulApprox_le` +
  `tendsto_umegakiNorm_faithful`), with the singular boundary continuity handled by
  the cross-term limit `tendsto_tr_perturb_mul_log_perturb`
  (and `tendsto_tr_faithful_cross` for the faithful path).

## The limit value

For positive-definite `ρ, σ`, L'Hôpital applied to
`D_α(ρ‖σ) = (α−1)⁻¹ · (log (Q_α).re − log (Tr ρ).re)` at `α = 1` gives

  `lim_{α → 1⁺} D_α(ρ‖σ) = (Tr ρ)⁻¹ · Re Tr(ρ (log ρ − log σ))`,

since `Q_1 = Tr ρ` makes the logarithm's argument tend to `1`, so the limit is the
derivative `(log ∘ Q)'(1) = Q'(1) / Q(1)` with
`Q'(1) = Re Tr(ρ(log ρ − log σ))`.

Cf. Frank–Lieb (arXiv:1306.5358v3): the `α = 1` case "follows by continuity in
α / a limiting argument".
-/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel MeasureTheory
open scoped ComplexOrder Topology

universe u

set_option linter.style.longLine false

section Umegaki

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

/-- **Normalised Umegaki relative entropy**
    `(Tr ρ)⁻¹ · Re Tr(ρ (log ρ − log σ))`.

    This is the `α → 1⁺` limit of `sandwichedRenyiDiv α ρ σ`
    (`sandwichedRenyiDiv_tendsto_umegaki`). For `ρ = 0` it evaluates to `0`
    (the `Tr ρ = 0` denominator gives `0 / 0 = 0`), matching the convention that
    the divergence vanishes when `ρ = 0`. -/
noncomputable def umegakiNorm (ρ σ : L ℋ) : ℝ :=
  (Tr (ρ * (CFC.log ρ - CFC.log σ))).re / (Tr ρ).re

/-- **Umegaki relative entropy** for non-negative `ρ, σ` (the `α → 1` boundary of
    the Frank–Lieb extension), as an `EReal`: value `⊤` on the support-mismatch
    region `¬ suppLE ρ σ`, and `umegakiNorm ρ σ` otherwise. -/
noncomputable def umegakiRelEntropyNN (ρ σ : L ℋ) : EReal :=
  letI : Decidable (suppLE ρ σ) := Classical.propDecidable _
  if suppLE ρ σ then ((umegakiNorm ρ σ : ℝ) : EReal) else (⊤ : EReal)

omit [Nontrivial ℋ] in
/-- The quasi-entropy at `α = 1` is `Tr ρ`: the conjugating power
    `σ^{(1−1)/(2·1)} = σ^0 = 1`, leaving `(1 ρ 1)^1 = ρ`. -/
lemma sandwichedQuasi_one_re (ρ σ : L ℋ) (hσ : 0 ≤ σ) (hρ : 0 ≤ ρ) :
    (sandwichedQuasi 1 ρ σ).re = (Tr ρ).re := by
  have h : sandwichedQuasi 1 ρ σ = Tr ρ := by
    unfold sandwichedQuasi
    have hz : CFC.rpow σ ((1 - (1 : ℝ)) / (2 * 1)) = 1 := by
      rw [show ((1 - (1 : ℝ)) / (2 * 1)) = 0 by norm_num]
      exact CFC.rpow_zero σ hσ
    rw [hz, one_mul, mul_one, show CFC.rpow ρ 1 = ρ from CFC.rpow_one ρ hρ]
  rw [h]

omit [Nontrivial ℋ] in
/-- Bridge: a `pdSetLM` operator is strictly positive (nonnegative and a unit). -/
lemma isStrictlyPositive_of_pdSetLM {σ : L ℋ} (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    IsStrictlyPositive σ := ⟨nonneg_of_pdSetLM hσ, isUnit_of_pdSetLM hσ⟩

omit [Nontrivial ℋ] in
/-- **Part B (proven): the conjugating-power contribution.** Differentiating the
    `α = 1` slice `α ↦ Re Tr(ρ · σ^{(1−α)/α})` (fixed base `σ`, exponent
    `(1−α)/α` with derivative `−1` at `α = 1`) gives `−Re Tr(ρ log σ)`.

    Proven from the fixed-base exponent derivative `CFC.hasDerivAt_rpow_exponent`
    (`CFCDeriv`), the chain rule, and `hasDerivAt_reTrace_mul_left`. -/
lemma hasDerivAt_partB {ρ σ : L ℋ} (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    HasDerivAt (fun α => (Tr (ρ * CFC.rpow σ ((1 - α) / α))).re)
      (-(Tr (ρ * CFC.log σ)).re) 1 := by
  have hσsp : IsStrictlyPositive σ := isStrictlyPositive_of_pdSetLM hσ
  have hσnn : (0 : L ℋ) ≤ σ := nonneg_of_pdSetLM hσ
  have ht : HasDerivAt (fun α : ℝ => (1 - α) / α) (-1) 1 := by
    have hu : HasDerivAt (fun α : ℝ => 1 - α) (-1) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).const_sub 1
    have hv : HasDerivAt (fun α : ℝ => α) (1) 1 := hasDerivAt_id 1
    simpa using hu.div hv (by norm_num)
  have hchain := CFC.hasDerivAt_rpow_exponent_comp hσsp ht
  have htr := hasDerivAt_reTrace_mul_left ρ hchain
  convert htr using 1
  have h0 : ((1 : ℝ) - 1) / 1 = 0 := by norm_num
  rw [h0, show CFC.rpow σ 0 = 1 from CFC.rpow_zero σ hσnn, one_mul]
  rw [show ((-1 : ℝ) • CFC.log σ) = -(CFC.log σ) from by simp]
  rw [mul_neg, map_neg, Complex.neg_re]

omit [Nontrivial ℋ] in
/-- **Cyclicity** identifying `Tr(ρ σ^{(1−α)/α})` with the trace of the inner operator
    `K(α) = σ^{(1−α)/(2α)} ρ σ^{(1−α)/(2α)}` of `sandwichedQuasi`. -/
lemma trace_conj_eq_trace_mul_rpow {ρ σ : L ℋ} (hσ : σ ∈ pdSetLM (ℋ := ℋ)) (α : ℝ) :
    Tr (ρ * CFC.rpow σ ((1 - α) / α))
      = Tr (CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α))) := by
  set c := (1 - α) / (2 * α) with hc
  have hσu : IsUnit σ := isUnit_of_pdSetLM hσ
  have hsum : (1 - α) / α = c + c := by rw [hc]; ring
  rw [hsum, show CFC.rpow σ (c + c) = CFC.rpow σ c * CFC.rpow σ c from CFC.rpow_add hσu,
     ← mul_assoc, LinearMap.trace_mul_comm, ← mul_assoc]



/-- **Averaging lemma** (general real analysis): if `g` is jointly continuous at `(a, a)`
    with value `L` and each `g α` is interval-integrable on `[a, α]`, then the average
    `(α − a)⁻¹ ∫_a^α g α s ds` tends to `L` as `α → a`. -/
lemma tendsto_average_of_continuousAt {g : ℝ → ℝ → ℝ} {a L : ℝ}
    (hcont : Filter.Tendsto (fun p : ℝ × ℝ => g p.1 p.2) (𝓝 (a, a)) (𝓝 L))
    (hint : ∀ α : ℝ, IntervalIntegrable (g α) volume a α) :
    Filter.Tendsto (fun α => (α - a)⁻¹ * ∫ s in a..α, g α s) (𝓝[≠] a) (𝓝 L) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  rw [Metric.tendsto_nhds_nhds] at hcont
  obtain ⟨δ, hδ, hball⟩ := hcont (ε / 2) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro α hα hdist
  have hαa : α - a ≠ 0 := sub_ne_zero.mpr hα
  have hsplit : ∫ s in a..α, g α s
      = (∫ s in a..α, (g α s - L)) + (α - a) * L := by
    rw [intervalIntegral.integral_sub (hint α) (intervalIntegral.intervalIntegrable_const),
        intervalIntegral.integral_const, smul_eq_mul]; ring
  have hbound : ∀ s ∈ Set.uIoc a α, ‖g α s - L‖ ≤ ε / 2 := by
    intro s hs
    have hs_dist : |s - a| ≤ |α - a| := by
      rcases Set.mem_uIoc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith), abs_of_neg (by linarith)]; linarith
    have hp_dist : dist (α, s) (a, a) < δ := by
      rw [Prod.dist_eq]; simp only [max_lt_iff, Real.dist_eq]
      exact ⟨hdist, lt_of_le_of_lt hs_dist (by rwa [Real.dist_eq] at hdist)⟩
    have hb := hball hp_dist
    rw [Real.dist_eq] at hb
    exact le_of_lt hb
  have hint_bound : ‖∫ s in a..α, (g α s - L)‖ ≤ (ε / 2) * |α - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hval : (α - a)⁻¹ * (∫ s in a..α, g α s) - L
      = (α - a)⁻¹ * (∫ s in a..α, (g α s - L)) := by
    rw [hsplit]; field_simp; ring
  rw [Real.dist_eq, hval, abs_mul, abs_inv]
  have hpos : (0 : ℝ) < |α - a| := abs_pos.mpr hαa
  calc |α - a|⁻¹ * |∫ s in a..α, (g α s - L)|
      ≤ |α - a|⁻¹ * ((ε / 2) * |α - a|) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rwa [← Real.norm_eq_abs]
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

omit [Nontrivial ℋ] in
/-- **FTC step.** For a strictly positive `K`, `Re Tr(K^α − K^1)` is the integral of
    `s ↦ Re Tr(K^s · log K)` over `[1, α]` (operator FTC + pushing `Re ∘ Tr` through). -/
lemma trace_rpow_sub_eq_integral {K : L ℋ} (hK : IsStrictlyPositive K) (α : ℝ) :
    (Tr (CFC.rpow K α - CFC.rpow K 1)).re
      = ∫ s in (1:ℝ)..α, (Tr (CFC.rpow K s * CFC.log K)).re := by
  have hcont : Continuous (fun s : ℝ => CFC.rpow K s * CFC.log K) :=
    (CFC.continuous_rpow_exponent hK).mul continuous_const
  have hop : (∫ s in (1:ℝ)..α, CFC.rpow K s * CFC.log K)
      = CFC.rpow K α - CFC.rpow K 1 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro s _; exact CFC.hasDerivAt_rpow_exponent hK s
    · exact hcont.intervalIntegrable _ _
  rw [← hop]
  have hii : IntervalIntegrable (fun s : ℝ => CFC.rpow K s * CFC.log K) volume 1 α :=
    hcont.intervalIntegrable 1 α
  have hcomm := (reTraceMulLeft (1 : L ℋ)).toContinuousLinearMap.intervalIntegral_comp_comm hii
  have key : ∀ X : L ℋ, (reTraceMulLeft (1 : L ℋ)).toContinuousLinearMap X = (Tr X).re := by
    intro X; simp [reTraceMulLeft]
  calc (Tr (∫ s in (1:ℝ)..α, CFC.rpow K s * CFC.log K)).re
      = (reTraceMulLeft (1 : L ℋ)).toContinuousLinearMap
          (∫ s in (1:ℝ)..α, CFC.rpow K s * CFC.log K) := (key _).symm
    _ = ∫ s in (1:ℝ)..α,
          (reTraceMulLeft (1 : L ℋ)).toContinuousLinearMap (CFC.rpow K s * CFC.log K) := hcomm.symm
    _ = ∫ s in (1:ℝ)..α, (Tr (CFC.rpow K s * CFC.log K)).re := by simp_rw [key]

omit [Nontrivial ℋ] in
/-- **Joint continuity** at `(1, 1)` of the FTC integrand
    `(α, s) ↦ Re Tr(K(α)^s · log K(α))`, `K(α) = σ^{(1−α)/(2α)} ρ σ^{(1−α)/(2α)}`.
    Proved via the exponential representation `K(α)^s = exp(s • log K(α))`
    (`CFC.rpow_eq_normedSpace_exp_smul_log`): this turns the cfc joint continuity into
    `(continuity of s • log K(α))` composed with the global continuity of `exp`,
    using `CFC.continuousOn_log` for the (element) continuity of `log K(α)`. -/
lemma continuousAt_quasiIntegrand {ρ σ : L ℋ}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    ContinuousAt (fun p : ℝ × ℝ =>
      (Tr (CFC.rpow (CFC.rpow σ ((1 - p.1) / (2 * p.1)) * ρ
              * CFC.rpow σ ((1 - p.1) / (2 * p.1))) p.2
          * CFC.log (CFC.rpow σ ((1 - p.1) / (2 * p.1)) * ρ
              * CFC.rpow σ ((1 - p.1) / (2 * p.1))))).re) (1, 1) := by
  set K : ℝ → L ℋ := fun α =>
    CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α)) with hKdef
  have hKpd : ∀ α, K α ∈ pdSetLM (ℋ := ℋ) := by
    intro α
    have hPpd : CFC.rpow σ ((1 - α) / (2 * α)) ∈ pdSetLM (ℋ := ℋ) := pdSetLM_rpow_ne hσ
    have hPsa : IsSelfAdjoint (CFC.rpow σ ((1 - α) / (2 * α))) :=
      IsSelfAdjoint.of_nonneg (nonneg_of_pdSetLM hPpd)
    have h := pdSetLM_conj hρ (isUnit_of_pdSetLM hPpd)
    rwa [hPsa.star_eq] at h
  have hKsp : ∀ α, IsStrictlyPositive (K α) := fun α =>
    ⟨nonneg_of_pdSetLM (hKpd α), isUnit_of_pdSetLM (hKpd α)⟩
  have hc : ContinuousAt (fun α : ℝ => (1 - α) / (2 * α)) 1 := by
    apply ContinuousAt.div <;> [fun_prop; fun_prop; norm_num]
  have hrpow : ContinuousAt (fun α : ℝ => CFC.rpow σ ((1 - α) / (2 * α))) 1 :=
    (CFC.continuous_rpow_exponent ⟨nonneg_of_pdSetLM hσ, isUnit_of_pdSetLM hσ⟩).continuousAt.comp hc
  have hK : ContinuousAt K 1 := (hrpow.mul continuousAt_const).mul hrpow
  have hmemS : ∀ α, K α ∈ {a : L ℋ | IsSelfAdjoint a ∧ IsUnit a} := fun α =>
    ⟨(hKsp α).1.isSelfAdjoint, (hKsp α).2⟩
  have hlogK : ContinuousAt (fun α => CFC.log (K α)) 1 := by
    have htend : Filter.Tendsto K (𝓝 1) (𝓝[{a : L ℋ | IsSelfAdjoint a ∧ IsUnit a}] (K 1)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hK
        (Filter.Eventually.of_forall hmemS)
    exact (CFC.continuousOn_log (K 1) (hmemS 1)).tendsto.comp htend
  have hfeq : (fun p : ℝ × ℝ => (Tr (CFC.rpow (K p.1) p.2 * CFC.log (K p.1))).re)
      = (fun p : ℝ × ℝ =>
          (Tr (NormedSpace.exp (p.2 • CFC.log (K p.1)) * CFC.log (K p.1))).re) := by
    funext p; rw [CFC.rpow_eq_normedSpace_exp_smul_log (hKsp p.1)]
  change ContinuousAt (fun p : ℝ × ℝ => (Tr (CFC.rpow (K p.1) p.2 * CFC.log (K p.1))).re) (1, 1)
  rw [hfeq]
  have h1 : ContinuousAt (fun p : ℝ × ℝ => CFC.log (K p.1)) ((1:ℝ), (1:ℝ)) :=
    ContinuousAt.comp (g := fun α => CFC.log (K α)) (f := Prod.fst)
      (x := ((1:ℝ), (1:ℝ))) hlogK continuousAt_fst
  have h2 : ContinuousAt (fun p : ℝ × ℝ => p.2 • CFC.log (K p.1)) ((1:ℝ), (1:ℝ)) :=
    continuousAt_snd.smul h1
  have h3 : ContinuousAt (fun p : ℝ × ℝ => NormedSpace.exp (p.2 • CFC.log (K p.1))) ((1:ℝ), (1:ℝ)) :=
    QuantumState.continuous_normedSpace_exp.continuousAt.comp h2
  exact QuantumState.continuous_re_trace.continuousAt.comp (h3.mul h1)

omit [Nontrivial ℋ] in
/-- **Part A** (proven): the outer-power contribution
    `α ↦ Re Tr(K(α)^α) − Re Tr(K(α))` (with `K(α) = σ^{(1−α)/(2α)} ρ σ^{(1−α)/(2α)}`,
    whose trace equals `Re Tr(ρ σ^{(1−α)/α})` by cyclicity) has derivative
    `Re Tr(ρ log ρ)` at `α = 1`.

    Fixed-base FTC + averaging (no Duhamel): `Re Tr(K(α)^α) − Re Tr(K(α))` is the
    integral of `g(α, s) := Re Tr(K(α)^s log K(α))` over `[1, α]`
    (`trace_rpow_sub_eq_integral`), so the difference quotient is the average of `g`,
    which tends to `g(1, 1) = Re Tr(ρ log ρ)` by `tendsto_average_of_continuousAt`
    and the joint continuity `continuousAt_quasiIntegrand`. -/
lemma hasDerivAt_partA {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    HasDerivAt (fun α => (sandwichedQuasi α ρ σ).re
        - (Tr (ρ * CFC.rpow σ ((1 - α) / α))).re) ((Tr (ρ * CFC.log ρ)).re) 1 := by
  set K : ℝ → L ℋ := fun α =>
    CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α)) with hKdef
  have hKpd : ∀ α, K α ∈ pdSetLM (ℋ := ℋ) := by
    intro α
    have hPpd : CFC.rpow σ ((1 - α) / (2 * α)) ∈ pdSetLM (ℋ := ℋ) := pdSetLM_rpow_ne hσ
    have hPsa : IsSelfAdjoint (CFC.rpow σ ((1 - α) / (2 * α))) :=
      IsSelfAdjoint.of_nonneg (nonneg_of_pdSetLM hPpd)
    have h := pdSetLM_conj hρ (isUnit_of_pdSetLM hPpd)
    rwa [hPsa.star_eq] at h
  have hKsp : ∀ α, IsStrictlyPositive (K α) := fun α =>
    ⟨nonneg_of_pdSetLM (hKpd α), isUnit_of_pdSetLM (hKpd α)⟩
  set g : ℝ → ℝ → ℝ := fun α s => (Tr (CFC.rpow (K α) s * CFC.log (K α))).re with hgdef
  have hK1 : K 1 = ρ := by
    have hP1 : CFC.rpow σ ((1 - (1:ℝ)) / (2 * 1)) = 1 := by
      rw [show ((1 - (1:ℝ)) / (2 * 1)) = 0 by norm_num]
      exact CFC.rpow_zero σ (nonneg_of_pdSetLM hσ)
    rw [hKdef]
    change CFC.rpow σ ((1 - (1:ℝ)) / (2 * 1)) * ρ * CFC.rpow σ ((1 - (1:ℝ)) / (2 * 1)) = ρ
    rw [hP1, one_mul, mul_one]
  have hg11 : g 1 1 = (Tr (ρ * CFC.log ρ)).re := by
    simp only [hgdef, hK1]
    rw [show CFC.rpow ρ 1 = ρ from CFC.rpow_one ρ (nonneg_of_pdSetLM hρ)]
  -- joint continuity of g at (1,1)
  have hjoint : ContinuousAt (fun p : ℝ × ℝ => g p.1 p.2) (1, 1) := by
    have := continuousAt_quasiIntegrand hρ hσ
    rwa [hgdef]
  -- integrability of g α
  have hint : ∀ α : ℝ, IntervalIntegrable (g α) volume 1 α := by
    intro α
    apply Continuous.intervalIntegrable
    rw [hgdef]
    exact QuantumState.continuous_re_trace.comp
      ((CFC.continuous_rpow_exponent (hKsp α)).mul continuous_const)
  -- averaging: the difference quotient tends to g 1 1
  have havg := tendsto_average_of_continuousAt hjoint hint
  -- HasDerivAt of the integral form
  have hF : HasDerivAt (fun α => ∫ s in (1:ℝ)..α, g α s) (g 1 1) 1 := by
    rw [hasDerivAt_iff_tendsto_slope]
    have hslope : slope (fun α => ∫ s in (1:ℝ)..α, g α s) 1
        = fun α => (α - 1)⁻¹ * ∫ s in (1:ℝ)..α, g α s := by
      funext α
      rw [slope_def_field, intervalIntegral.integral_same, sub_zero, div_eq_inv_mul]
    rw [hslope]; exact havg
  -- the Part A function equals the integral form
  have hfunc : (fun α => (sandwichedQuasi α ρ σ).re - (Tr (ρ * CFC.rpow σ ((1 - α) / α))).re)
      = (fun α => ∫ s in (1:ℝ)..α, g α s) := by
    funext α
    have hsq : (sandwichedQuasi α ρ σ).re = (Tr (CFC.rpow (K α) α)).re := by rw [hKdef]; rfl
    have hcyc : (Tr (ρ * CFC.rpow σ ((1 - α) / α))).re = (Tr (CFC.rpow (K α) 1)).re := by
      rw [trace_conj_eq_trace_mul_rpow hσ α,
        show CFC.rpow (K α) 1 = K α from CFC.rpow_one (K α) (nonneg_of_pdSetLM (hKpd α)), hKdef]
    rw [hsq, hcyc, ← Complex.sub_re, ← map_sub, trace_rpow_sub_eq_integral (hKsp α) α, hgdef]
  rw [hfunc, ← hg11]
  exact hF

omit [Nontrivial ℋ] in
/-- The derivative at `α = 1` of the real quasi-entropy
    `α ↦ Re Tr((σ^{(1−α)/(2α)} ρ σ^{(1−α)/(2α)})^α)` is `Re Tr(ρ (log ρ − log σ))`.

    Assembled from Part A (`hasDerivAt_partA`) and Part B (`hasDerivAt_partB`):
    the quasi-entropy splits as `(Q − Tr K) + Tr K`, whose derivatives are
    `Re Tr(ρ log ρ)` and `−Re Tr(ρ log σ)`. -/
lemma hasDerivAt_sandwichedQuasi_re_one
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    HasDerivAt (fun α => (sandwichedQuasi α ρ σ).re)
      ((Tr (ρ * (CFC.log ρ - CFC.log σ))).re) 1 := by
  have hB := hasDerivAt_partB (ρ := ρ) hσ
  have hA := hasDerivAt_partA hρ hσ
  have hsum := hA.add hB
  have heq : (fun α => (sandwichedQuasi α ρ σ).re)
      = (fun α => (sandwichedQuasi α ρ σ).re - (Tr (ρ * CFC.rpow σ ((1 - α) / α))).re)
        + (fun α => (Tr (ρ * CFC.rpow σ ((1 - α) / α))).re) := by
    funext α; simp only [Pi.add_apply]; ring
  rw [heq]
  convert hsum using 1
  rw [mul_sub, map_sub, Complex.sub_re]; ring

/-- **The `α → 1⁺` limit of the sandwiched Rényi divergence is the Umegaki
    relative entropy**, for positive-definite `ρ, σ`.

    Fully proven as a difference-quotient limit: with `Q(α) := (Q_α ρ σ).re` and
    `Q(1) = (Tr ρ).re`, one has
    `D_α(ρ‖σ) = (log Q(α) − log Q(1)) / (α − 1) = slope (log ∘ Q) 1 α`, and this
    slope tends to `(log ∘ Q)'(1) = umegakiNorm ρ σ` (by `hasDerivAt_iff_tendsto_slope`,
    restricted to `𝓝[>] 1`). The single derivative input is
    `hasDerivAt_sandwichedQuasi_re_one`. -/
lemma sandwichedRenyiDiv_tendsto_umegaki
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    Filter.Tendsto (fun α => sandwichedRenyiDiv α ρ σ) (𝓝[>] (1 : ℝ))
      (𝓝 (umegakiNorm ρ σ)) := by
  have hρ_nn := nonneg_of_pdSetLM hρ
  have hσ_nn := nonneg_of_pdSetLM hσ
  have hTrρ_pos : 0 < (Tr ρ).re := trace_re_pos_of_pdSetLM hρ
  have hQ1 : (sandwichedQuasi 1 ρ σ).re = (Tr ρ).re := sandwichedQuasi_one_re ρ σ hσ_nn hρ_nn
  have hQ1_ne : (sandwichedQuasi 1 ρ σ).re ≠ 0 := by rw [hQ1]; exact ne_of_gt hTrρ_pos
  -- chain rule for `log ∘ (Q_α).re` at `α = 1`
  have hderiv_f := hasDerivAt_sandwichedQuasi_re_one hρ hσ
  have hderiv_logf : HasDerivAt (fun α => Real.log ((sandwichedQuasi α ρ σ).re))
      (umegakiNorm ρ σ) 1 := by
    have hch := hderiv_f.log hQ1_ne
    rw [hQ1] at hch
    exact hch
  -- a derivative is the limit of the slope; restrict `𝓝[≠] 1` to `𝓝[>] 1`
  rw [hasDerivAt_iff_tendsto_slope] at hderiv_logf
  have h_mono : 𝓝[>] (1 : ℝ) ≤ 𝓝[≠] (1 : ℝ) :=
    nhdsWithin_mono _ (fun x hx => ne_of_gt hx)
  have h_slope := hderiv_logf.mono_left h_mono
  -- on `𝓝[>] 1`, the divergence coincides with that slope
  refine h_slope.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with α hα
  have hα1 : (1 : ℝ) < α := hα
  have hα0 : (0 : ℝ) < α := by linarith
  have hfα_ne : (sandwichedQuasi α ρ σ).re ≠ 0 := sandwichedQuasi_re_ne_zero_of_pdSetLM hα0 hρ hσ
  change slope (fun α => Real.log ((sandwichedQuasi α ρ σ).re)) 1 α = sandwichedRenyiDiv α ρ σ
  rw [slope_def_field]
  unfold sandwichedRenyiDiv
  rw [hQ1, Real.log_div hfα_ne (ne_of_gt hTrρ_pos), one_div]
  ring

/-- **Data-processing for the Umegaki relative entropy, positive-definite case.**

    Fully reduced to `sandwichedRenyiDiv_tendsto_umegaki`: the finite-`α`
    monotonicity `sandwichedRenyiDiv_monotone` holds for every `α > 1`, and both
    sides converge to `umegakiNorm` as `α → 1⁺`, so the inequality passes to the
    limit. -/
theorem umegakiNorm_monotone_pd
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] (E : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ))
    (hEρ : E.toFun ρ ∈ pdSetLM (ℋ := 𝒦)) (hEσ : E.toFun σ ∈ pdSetLM (ℋ := 𝒦)) :
    umegakiNorm (E.toFun ρ) (E.toFun σ) ≤ umegakiNorm ρ σ := by
  have hlim1 := sandwichedRenyiDiv_tendsto_umegaki hEρ hEσ
  have hlim2 := sandwichedRenyiDiv_tendsto_umegaki hρ hσ
  refine le_of_tendsto_of_tendsto hlim1 hlim2 ?_
  filter_upwards [self_mem_nhdsWithin] with α hα
  have hα1 : (1 : ℝ) < α := hα
  exact sandwichedRenyiDiv_monotone E (by linarith) (ne_of_gt hα1) hρ hσ hEρ hEσ

/-- Boundary continuity of the cross term `Re Tr((ρ+ε)·log(σ+ε)) → Re Tr(ρ·log σ)`
    for nonneg `ρ, σ` with `supp ρ ⊆ supp σ` (finite at singular `σ` since `ρ` kills
    `ker σ`, so the divergent `log ε` on `ker σ` enters only via `ε·log ε → 0`). -/
lemma tendsto_tr_perturb_mul_log_perturb {ρ σ : L ℋ}
    (hσ : 0 ≤ σ) (hsupp : suppLE ρ σ) :
    Filter.Tendsto (fun ε : ℝ => (Tr ((ρ + (ε : ℂ) • 1) * CFC.log (σ + (ε : ℂ) • 1))).re)
      (𝓝[>] (0:ℝ)) (𝓝 ((Tr (ρ * CFC.log σ)).re)) := by
  classical
  have hσ_sa : IsSelfAdjoint σ := IsSelfAdjoint.of_nonneg hσ
  have hσ_pos : σ.IsPositive := (LinearMap.nonneg_iff_isPositive σ).mp hσ
  have hσ_sym := hσ_pos.isSymmetric
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  set b := hσ_sym.eigenvectorBasis hn with hb
  set eig := hσ_sym.eigenvalues hn with heig
  have h_eig_apply : ∀ i, σ (b i) = ((eig i : ℝ) : ℂ) • b i := hσ_sym.apply_eigenvectorBasis hn
  have hb_ne : ∀ i, b i ≠ 0 := fun i => b.orthonormal.ne_zero i
  have hbb : ∀ i, inner ℂ (b i) (b i) = (1 : ℂ) := fun i => b.inner_eq_one i
  set c : Fin n → ℝ := fun i => (inner ℂ (b i) (ρ (b i))).re with hc_def
  have hc0 : ∀ i, eig i = 0 → c i = 0 := by
    intro i hi
    have hbker : b i ∈ LinearMap.ker σ := by rw [LinearMap.mem_ker, h_eig_apply i, hi]; simp
    have hρb : ρ (b i) = 0 := LinearMap.mem_ker.mp (hsupp hbker)
    simp only [hc_def, hρb, inner_zero_right, Complex.zero_re]
  have hev : ∀ (ε : ℝ) (i), (σ + (ε : ℂ) • (1 : L ℋ)) (b i) = ((eig i + ε : ℝ) : ℂ) • b i := by
    intro ε i
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, h_eig_apply i]
    rw [← add_smul]; norm_cast
  have hsa : ∀ (ε : ℝ), IsSelfAdjoint (σ + (ε : ℂ) • (1 : L ℋ)) := by
    intro ε
    rw [IsSelfAdjoint, star_add, hσ_sa.star_eq, star_smul, star_one, Complex.star_def,
      Complex.conj_ofReal]
  have hlog_apply : ∀ (ε : ℝ) (i),
      CFC.log (σ + (ε : ℂ) • 1) (b i) = ((Real.log (eig i + ε) : ℝ) : ℂ) • b i := by
    intro ε i
    exact cfc_real_apply_eigenvector (hsa ε) Real.log (hev ε i)
      (mem_spectrum_real_of_eigenvector (hb_ne i) (hev ε i))
  have hinner : ∀ (ε : ℝ) (i),
      (inner ℂ (b i) ((ρ + (ε : ℂ) • 1) (b i))).re = c i + ε := by
    intro ε i
    rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, inner_add_right,
      inner_smul_right, hbb i, mul_one, Complex.add_re, hc_def, Complex.ofReal_re]
  have hexpand : ∀ ε : ℝ, (Tr ((ρ + (ε : ℂ) • 1) * CFC.log (σ + (ε : ℂ) • 1))).re
      = ∑ i, Real.log (eig i + ε) * (c i + ε) := by
    intro ε
    rw [LinearMap.trace_eq_sum_inner (T := (ρ + (ε : ℂ) • 1) * CFC.log (σ + (ε : ℂ) • 1)) b,
      Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Module.End.mul_apply, hlog_apply ε i, map_smul, inner_smul_right, Complex.re_ofReal_mul,
      hinner ε i]
  have hlimval : (Tr (ρ * CFC.log σ)).re = ∑ i, Real.log (eig i) * c i := by
    have h0 := hexpand 0
    simp only [Complex.ofReal_zero, zero_smul, add_zero] at h0
    exact h0
  rw [hlimval, show (fun ε : ℝ => (Tr ((ρ + (ε : ℂ) • 1) * CFC.log (σ + (ε : ℂ) • 1))).re)
        = (fun ε => ∑ i, Real.log (eig i + ε) * (c i + ε)) from funext hexpand]
  apply tendsto_finset_sum
  intro i _
  have haddci : Filter.Tendsto (fun ε : ℝ => c i + ε) (𝓝[>] (0:ℝ)) (𝓝 (c i)) := by
    have : Filter.Tendsto (fun ε : ℝ => c i + ε) (𝓝 (0:ℝ)) (𝓝 (c i + 0)) :=
      (continuous_const.add continuous_id).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  by_cases hi : eig i = 0
  · rw [hi, hc0 i hi]
    simp only [Real.log_zero, mul_zero, zero_add]
    have hnml : Filter.Tendsto (fun ε : ℝ => Real.log ε * ε) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hc := (Real.continuous_negMulLog.tendsto 0)
      simp only [Real.negMulLog_zero] at hc
      have := hc.neg
      simp only [neg_zero] at this
      refine (this.mono_left nhdsWithin_le_nhds).congr (fun ε => ?_)
      simp [Real.negMulLog, mul_comm]
    exact hnml
  · have heig_pos : 0 < eig i :=
      lt_of_le_of_ne (hσ_pos.nonneg_eigenvalues hn i) (Ne.symm hi)
    have hlog : Filter.Tendsto (fun ε : ℝ => Real.log (eig i + ε)) (𝓝[>] (0:ℝ))
        (𝓝 (Real.log (eig i))) := by
      have : Filter.Tendsto (fun ε : ℝ => Real.log (eig i + ε)) (𝓝 (0:ℝ))
          (𝓝 (Real.log (eig i + 0))) :=
        (Real.continuousAt_log (by simpa using ne_of_gt heig_pos)).comp
          ((continuous_const.add continuous_id).tendsto 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    exact hlog.mul haddci

omit [Nontrivial ℋ] in
/-- `Re Tr(ρ + ε•1) → Re Tr ρ` as `ε → 0⁺`. -/
lemma tendsto_tr_perturb {ρ : L ℋ} :
    Filter.Tendsto (fun ε : ℝ => (Tr (ρ + (ε : ℂ) • 1)).re) (𝓝[>] (0:ℝ)) (𝓝 (Tr ρ).re) := by
  have key : (Tr ρ).re = (Tr (ρ + ((0:ℝ) : ℂ) • (1 : L ℋ))).re := by simp
  rw [key]
  exact ((QuantumState.continuous_re_trace.comp
    (by fun_prop : Continuous fun ε : ℝ => ρ + (ε : ℂ) • (1 : L ℋ))).tendsto 0).mono_left
    nhdsWithin_le_nhds

/-- **Boundary continuity (H1)**: `umegakiNorm (ρ+ε) (σ+ε) → umegakiNorm ρ σ` as `ε → 0⁺`,
    for nonneg `ρ ≠ 0`, `σ` with `supp ρ ⊆ supp σ`. Assembles the cross-term continuity
    (numerator) with trace continuity (denominator) via `Tendsto.div`. -/
lemma tendsto_umegakiNorm_perturb {ρ σ : L ℋ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0) (hsupp : suppLE ρ σ) :
    Filter.Tendsto (fun ε : ℝ => umegakiNorm (ρ + (ε : ℂ) • 1) (σ + (ε : ℂ) • 1))
      (𝓝[>] (0:ℝ)) (𝓝 (umegakiNorm ρ σ)) := by
  have hcrossρ := tendsto_tr_perturb_mul_log_perturb (ρ := ρ) (σ := ρ) hρ (le_refl _)
  have hcrossσ := tendsto_tr_perturb_mul_log_perturb (ρ := ρ) (σ := σ) hσ hsupp
  have hnum : Filter.Tendsto
      (fun ε : ℝ => (Tr ((ρ + (ε : ℂ) • 1) *
          (CFC.log (ρ + (ε : ℂ) • 1) - CFC.log (σ + (ε : ℂ) • 1)))).re)
      (𝓝[>] (0:ℝ)) (𝓝 ((Tr (ρ * (CFC.log ρ - CFC.log σ))).re)) := by
    have heqf : (fun ε : ℝ => (Tr ((ρ + (ε : ℂ) • 1) *
          (CFC.log (ρ + (ε : ℂ) • 1) - CFC.log (σ + (ε : ℂ) • 1)))).re)
        = (fun ε : ℝ => (Tr ((ρ + (ε : ℂ) • 1) * CFC.log (ρ + (ε : ℂ) • 1))).re
            - (Tr ((ρ + (ε : ℂ) • 1) * CFC.log (σ + (ε : ℂ) • 1))).re) := by
      funext ε; rw [mul_sub, map_sub, Complex.sub_re]
    rw [heqf, show (Tr (ρ * (CFC.log ρ - CFC.log σ))).re
          = (Tr (ρ * CFC.log ρ)).re - (Tr (ρ * CFC.log σ)).re from by
        rw [mul_sub, map_sub, Complex.sub_re]]
    exact hcrossρ.sub hcrossσ
  have hden0 : (Tr ρ).re ≠ 0 := ne_of_gt (trace_re_pos_of_ne_zero hρ hρ0)
  have hres := hnum.div (tendsto_tr_perturb (ρ := ρ)) hden0
  simpa only [umegakiNorm] using hres

/-- **Continuity of `umegakiNorm` along a path into the strictly-positive operators**
    (no singularity): if `a ε → a₀`, `b ε → b₀` with `a ε, b ε` eventually
    self-adjoint units and `a₀, b₀` self-adjoint units (`Re Tr a₀ ≠ 0`), then
    `umegakiNorm (a ε) (b ε) → umegakiNorm a₀ b₀`. Uses `CFC.continuousOn_log`. -/
lemma tendsto_umegakiNorm_within {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {a b : ℝ → L 𝒦} {a₀ b₀ : L 𝒦} {l : Filter ℝ}
    (ha : Filter.Tendsto a l (𝓝 a₀)) (hb : Filter.Tendsto b l (𝓝 b₀))
    (ha_mem : ∀ᶠ ε in l, IsSelfAdjoint (a ε) ∧ IsUnit (a ε))
    (hb_mem : ∀ᶠ ε in l, IsSelfAdjoint (b ε) ∧ IsUnit (b ε))
    (ha0 : IsSelfAdjoint a₀ ∧ IsUnit a₀) (hb0 : IsSelfAdjoint b₀ ∧ IsUnit b₀)
    (hTra0 : (Tr a₀).re ≠ 0) :
    Filter.Tendsto (fun ε => umegakiNorm (a ε) (b ε)) l (𝓝 (umegakiNorm a₀ b₀)) := by
  have hloga : Filter.Tendsto (fun ε => CFC.log (a ε)) l (𝓝 (CFC.log a₀)) :=
    (CFC.continuousOn_log a₀ ha0).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ha ha_mem)
  have hlogb : Filter.Tendsto (fun ε => CFC.log (b ε)) l (𝓝 (CFC.log b₀)) :=
    (CFC.continuousOn_log b₀ hb0).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hb hb_mem)
  have hnum : Filter.Tendsto (fun ε => (Tr (a ε * (CFC.log (a ε) - CFC.log (b ε)))).re) l
      (𝓝 ((Tr (a₀ * (CFC.log a₀ - CFC.log b₀))).re)) :=
    (QuantumState.continuous_re_trace.tendsto _).comp (ha.mul (hloga.sub hlogb))
  have hden : Filter.Tendsto (fun ε => (Tr (a ε)).re) l (𝓝 (Tr a₀).re) :=
    (QuantumState.continuous_re_trace.tendsto _).comp ha
  simpa only [umegakiNorm] using hnum.div hden hTra0

/-- **step1**: for each faithful parameter `λ ∈ (0,1]`,
    `umegakiNorm (F_λ ρ) (F_λ σ) ≤ umegakiNorm ρ σ`. Proven by perturbing inputs to
    `ρ+ε, σ+ε` (pd), applying the pd DPI `umegakiNorm_monotone_pd`, and taking `ε → 0⁺`
    (RHS via `tendsto_umegakiNorm_perturb`, LHS via `tendsto_umegakiNorm_within` since
    `F_λ` outputs are pd). -/
lemma umegakiNorm_faithfulApprox_le {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0) (hsupp : suppLE ρ σ)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    umegakiNorm ((faithfulApprox E lam hlam0.le hlam1).toFun ρ)
        ((faithfulApprox E lam hlam0.le hlam1).toFun σ) ≤ umegakiNorm ρ σ := by
  have hσ0 : σ ≠ 0 := by
    rintro rfl; apply hρ0
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply]
    exact LinearMap.mem_ker.mp (hsupp (LinearMap.mem_ker.mpr (by simp)))
  set F := faithfulApprox E lam hlam0.le hlam1 with hF
  have hFρ : F.toFun ρ ∈ pdSetLM (ℋ := 𝒦) := faithfulApprox_pdSetLM E hlam0 hlam1 hρ hρ0
  have hFσ : F.toFun σ ∈ pdSetLM (ℋ := 𝒦) := faithfulApprox_pdSetLM E hlam0 hlam1 hσ hσ0
  have hFcont : Continuous (fun ε : ℝ => F.toFun (ρ + (ε : ℂ) • 1)) :=
    (LinearMap.continuous_of_finiteDimensional F.toCompletelyPositiveMap.toLinearMap).comp
      (by fun_prop)
  have hFcontσ : Continuous (fun ε : ℝ => F.toFun (σ + (ε : ℂ) • 1)) :=
    (LinearMap.continuous_of_finiteDimensional F.toCompletelyPositiveMap.toLinearMap).comp
      (by fun_prop)
  have h_pert : ∀ ε : ℝ, 0 < ε →
      umegakiNorm (F.toFun (ρ + (ε : ℂ) • 1)) (F.toFun (σ + (ε : ℂ) • 1))
        ≤ umegakiNorm (ρ + (ε : ℂ) • 1) (σ + (ε : ℂ) • 1) := by
    intro ε hε
    have hρε : ρ + (ε : ℂ) • 1 ∈ pdSetLM (ℋ := ℋ) := pdSetLM_add_nonneg hρ (pos_smul_one_pdSetLM hε)
    have hσε : σ + (ε : ℂ) • 1 ∈ pdSetLM (ℋ := ℋ) := pdSetLM_add_nonneg hσ (pos_smul_one_pdSetLM hε)
    exact umegakiNorm_monotone_pd F hρε hσε
      (faithfulApprox_pdSetLM E hlam0 hlam1 (nonneg_of_pdSetLM hρε) (isUnit_of_pdSetLM hρε).ne_zero)
      (faithfulApprox_pdSetLM E hlam0 hlam1 (nonneg_of_pdSetLM hσε) (isUnit_of_pdSetLM hσε).ne_zero)
  have h_RHS := tendsto_umegakiNorm_perturb hρ hσ hρ0 hsupp
  have h_LHS : Filter.Tendsto
      (fun ε : ℝ => umegakiNorm (F.toFun (ρ + (ε : ℂ) • 1)) (F.toFun (σ + (ε : ℂ) • 1)))
      (𝓝[>] (0:ℝ)) (𝓝 (umegakiNorm (F.toFun ρ) (F.toFun σ))) := by
    have hpd2sa : ∀ {τ : L 𝒦}, τ ∈ pdSetLM (ℋ := 𝒦) → IsSelfAdjoint τ ∧ IsUnit τ :=
      fun hτ => ⟨IsSelfAdjoint.of_nonneg (nonneg_of_pdSetLM hτ), isUnit_of_pdSetLM hτ⟩
    have hKey : F.toFun ρ = F.toFun (ρ + ((0:ℝ) : ℂ) • 1) := by simp
    have hKeyσ : F.toFun σ = F.toFun (σ + ((0:ℝ) : ℂ) • 1) := by simp
    refine tendsto_umegakiNorm_within
      (a := fun ε => F.toFun (ρ + (ε : ℂ) • 1)) (b := fun ε => F.toFun (σ + (ε : ℂ) • 1))
      (a₀ := F.toFun ρ) (b₀ := F.toFun σ)
      (hKey ▸ (hFcont.tendsto 0).mono_left nhdsWithin_le_nhds)
      (hKeyσ ▸ (hFcontσ.tendsto 0).mono_left nhdsWithin_le_nhds)
      ?_ ?_ (hpd2sa hFρ) (hpd2sa hFσ) (ne_of_gt (trace_re_pos_of_pdSetLM hFρ))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hρε : ρ + (ε : ℂ) • 1 ∈ pdSetLM (ℋ := ℋ) := pdSetLM_add_nonneg hρ (pos_smul_one_pdSetLM hε)
      exact hpd2sa (faithfulApprox_pdSetLM E hlam0 hlam1 (nonneg_of_pdSetLM hρε)
        (isUnit_of_pdSetLM hρε).ne_zero)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hσε : σ + (ε : ℂ) • 1 ∈ pdSetLM (ℋ := ℋ) := pdSetLM_add_nonneg hσ (pos_smul_one_pdSetLM hε)
      exact hpd2sa (faithfulApprox_pdSetLM E hlam0 hlam1 (nonneg_of_pdSetLM hσε)
        (isUnit_of_pdSetLM hσε).ne_zero)
  haveI : (𝓝[>] (0:ℝ)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
  exact le_of_tendsto_of_tendsto h_LHS h_RHS (Filter.eventually_of_mem self_mem_nhdsWithin h_pert)

lemma tendsto_uloglu : Filter.Tendsto (fun u : ℝ => u * Real.log u) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hc0 := (Real.continuous_negMulLog.tendsto 0)
  simp only [Real.negMulLog_zero] at hc0
  have h := hc0.neg
  simp only [neg_zero] at h
  refine (h.mono_left nhdsWithin_le_nhds).congr (fun u => ?_)
  simp [Real.negMulLog]

lemma tendsto_lam_log_lam_mul {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun lam : ℝ => lam * Real.log (lam * c)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hu : Filter.Tendsto (fun lam : ℝ => lam * c) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using ((continuous_mul_const c).tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with lam hlam
      exact mul_pos hlam hc
  have hcomp := (tendsto_uloglu.comp hu).const_mul (c⁻¹)
  simp only [mul_zero] at hcomp
  refine hcomp.congr fun lam => ?_
  simp only [Function.comp_apply]
  field_simp
end Umegaki
end SandwichedRenyiRelativeEntropy


