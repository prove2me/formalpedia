-- Prove2me | Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiUmegaki_part_2
-- name    : CRCD_Quantum_QuantumEntropy_SandwichedRenyiUmegaki_part_2
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T02:08:54.582011+00:00
-- url     : https://prove2.me/theorems/a2907fec-329f-417a-81b0-50b3c555d1dd
-- title:
--   Faithful limits and support-aware Umegaki data processing
-- statement:
--   Let $\Phi:L(H)\to L(K)$ be CPTP on nonzero finite-dimensional complex Hilbert spaces, with $d_K=\dim K$. For $\tau\ge0$ and $0\le\lambda\le1$, the faithful approximation has the explicit form
--   $$
--   F_\lambda(\tau)=(1-\lambda)\Phi(\tau)+\lambda\frac{\operatorname{Re}\operatorname{Tr}\tau}{d_K}I_K.
--   $$
--   For $\rho,\sigma\ge0$, $\rho\ne0$ and $\ker\sigma\subseteq\ker\rho$, the part proves $U(F_\lambda(\rho)\Vert F_\lambda(\sigma))\to U(\Phi(\rho)\Vert\Phi(\sigma))$ as $\lambda\to0^+$ through $(0,1]$, and also proves the corresponding real-parameter limit for the displayed operator expressions.
--
--   The final data-processing statements are
--   $$
--   U(\Phi(\rho)\Vert\Phi(\sigma))\le U(\rho\Vert\sigma)
--   \quad\text{if }\rho,\sigma\ge0,\ \ker\sigma\subseteq\ker\rho,
--   $$
--   $$
--   U^{\mathrm{NN}}(\Phi(\rho)\Vert\Phi(\sigma))\le U^{\mathrm{NN}}(\rho\Vert\sigma)
--   \quad\text{if }\rho,\sigma\ge0.
--   $$
--   The first includes $\rho=0$; the second includes support mismatch and $+\infty$. $U$ is trace-normalized and uses natural operator logarithms, while $U^{\mathrm{NN}}$ takes the value $+\infty$ off support. No unit-trace premise or bit conversion is imposed.
--
--   A supporting cross-term limit states $\operatorname{Re}\operatorname{Tr}[B_\lambda\log A_\lambda]\to\operatorname{Re}\operatorname{Tr}(B\log A)$ for $A,B\ge0$, $\ker A\subseteq\ker B$, $A_\lambda=(1-\lambda)A+\lambda c_AI$, $B_\lambda=(1-\lambda)B+\lambda c_BI$, with $c_A>0$ and arbitrary real $c_B$. Finally, positive semidefinite operators have real trace and satisfy $\|C\|\le\operatorname{Re}\operatorname{Tr}C$.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumEntropy/SandwichedRenyiUmegaki.lean#L650-L958

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
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiUmegaki_part_1
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











































lemma tendsto_tr_faithful_cross {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] {A B : L 𝒦}
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (hsupp : suppLE B A) {cA cB : ℝ} (hcA : 0 < cA) :
    Filter.Tendsto (fun lam : ℝ =>
        (Tr ((((1 - lam : ℝ) : ℂ) • B + ((lam * cB : ℝ) : ℂ) • 1) *
          CFC.log (((1 - lam : ℝ) : ℂ) • A + ((lam * cA : ℝ) : ℂ) • 1))).re)
      (𝓝[>] (0:ℝ)) (𝓝 ((Tr (B * CFC.log A)).re)) := by
  classical
  have hA_sa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  have hA_pos : A.IsPositive := (LinearMap.nonneg_iff_isPositive A).mp hA
  have hA_sym := hA_pos.isSymmetric
  set n := Module.finrank ℂ 𝒦 with hn_def
  have hn : Module.finrank ℂ 𝒦 = n := rfl
  set b := hA_sym.eigenvectorBasis hn with hb
  set eig := hA_sym.eigenvalues hn with heig
  have h_eig_apply : ∀ i, A (b i) = ((eig i : ℝ) : ℂ) • b i := hA_sym.apply_eigenvectorBasis hn
  have hb_ne : ∀ i, b i ≠ 0 := fun i => b.orthonormal.ne_zero i
  have hbb : ∀ i, inner ℂ (b i) (b i) = (1 : ℂ) := fun i => b.inner_eq_one i
  set d : Fin n → ℝ := fun i => (inner ℂ (b i) (B (b i))).re with hd_def
  have hd0 : ∀ i, eig i = 0 → d i = 0 := by
    intro i hi
    have hbker : b i ∈ LinearMap.ker A := by rw [LinearMap.mem_ker, h_eig_apply i, hi]; simp
    have hBb : B (b i) = 0 := LinearMap.mem_ker.mp (hsupp hbker)
    simp only [hd_def, hBb, inner_zero_right, Complex.zero_re]
  have hev : ∀ (lam : ℝ) (i),
      (((1 - lam : ℝ) : ℂ) • A + ((lam * cA : ℝ) : ℂ) • (1 : L 𝒦)) (b i)
        = (((1 - lam) * eig i + lam * cA : ℝ) : ℂ) • b i := by
    intro lam i
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, h_eig_apply i,
      smul_smul]
    rw [← add_smul]; push_cast; ring_nf
  have hsa : ∀ (lam : ℝ), IsSelfAdjoint (((1 - lam : ℝ) : ℂ) • A + ((lam * cA : ℝ) : ℂ) • (1 : L 𝒦)) := by
    intro lam
    rw [IsSelfAdjoint, star_add, star_smul, hA_sa.star_eq, star_smul, star_one,
      Complex.star_def, Complex.conj_ofReal, Complex.conj_ofReal]
  have hlog_apply : ∀ (lam : ℝ) (i),
      CFC.log (((1 - lam : ℝ) : ℂ) • A + ((lam * cA : ℝ) : ℂ) • 1) (b i)
        = ((Real.log ((1 - lam) * eig i + lam * cA) : ℝ) : ℂ) • b i := by
    intro lam i
    exact cfc_real_apply_eigenvector (hsa lam) Real.log (hev lam i)
      (mem_spectrum_real_of_eigenvector (hb_ne i) (hev lam i))
  have hinner : ∀ (lam : ℝ) (i),
      (inner ℂ (b i) ((((1 - lam : ℝ) : ℂ) • B + ((lam * cB : ℝ) : ℂ) • 1) (b i))).re
        = (1 - lam) * d i + lam * cB := by
    intro lam i
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply,
      inner_add_right, inner_smul_right, inner_smul_right, hbb i, mul_one, Complex.add_re,
      Complex.re_ofReal_mul, Complex.ofReal_re, hd_def]
  have hexpand : ∀ lam : ℝ,
      (Tr ((((1 - lam : ℝ) : ℂ) • B + ((lam * cB : ℝ) : ℂ) • 1) *
          CFC.log (((1 - lam : ℝ) : ℂ) • A + ((lam * cA : ℝ) : ℂ) • 1))).re
        = ∑ i, Real.log ((1 - lam) * eig i + lam * cA) * ((1 - lam) * d i + lam * cB) := by
    intro lam
    rw [LinearMap.trace_eq_sum_inner
        (T := (((1 - lam : ℝ) : ℂ) • B + ((lam * cB : ℝ) : ℂ) • 1) *
          CFC.log (((1 - lam : ℝ) : ℂ) • A + ((lam * cA : ℝ) : ℂ) • 1)) b, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Module.End.mul_apply, hlog_apply lam i, map_smul, inner_smul_right, Complex.re_ofReal_mul,
      hinner lam i]
  have hlimval : (Tr (B * CFC.log A)).re = ∑ i, Real.log (eig i) * d i := by
    have h0 := hexpand 0
    simp only [sub_zero, Complex.ofReal_one, one_smul, zero_mul, Complex.ofReal_zero, zero_smul,
      add_zero, one_mul] at h0
    exact h0
  rw [hlimval, show (fun lam : ℝ =>
        (Tr ((((1 - lam : ℝ) : ℂ) • B + ((lam * cB : ℝ) : ℂ) • 1) *
          CFC.log (((1 - lam : ℝ) : ℂ) • A + ((lam * cA : ℝ) : ℂ) • 1))).re)
      = (fun lam => ∑ i, Real.log ((1 - lam) * eig i + lam * cA) * ((1 - lam) * d i + lam * cB))
        from funext hexpand]
  apply tendsto_finset_sum
  intro i _
  by_cases hi : eig i = 0
  · rw [hi, hd0 i hi]
    simp only [mul_zero, zero_add, Real.log_zero]
    -- term = log(lam*cA) * (lam*cB) → 0 ; target log 0 * 0 = 0
    have : Filter.Tendsto (fun lam : ℝ => Real.log (lam * cA) * (lam * cB)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hh := (tendsto_lam_log_lam_mul hcA).const_mul cB
      simp only [mul_zero] at hh
      refine hh.congr fun lam => ?_
      ring
    simpa using this
  · have heig_pos : 0 < eig i := lt_of_le_of_ne (hA_pos.nonneg_eigenvalues hn i) (Ne.symm hi)
    have hlogt : Filter.Tendsto (fun lam : ℝ => Real.log ((1 - lam) * eig i + lam * cA))
        (𝓝[>] (0:ℝ)) (𝓝 (Real.log (eig i))) := by
      have hin : Filter.Tendsto (fun lam : ℝ => (1 - lam) * eig i + lam * cA) (𝓝 (0:ℝ))
          (𝓝 (eig i)) := by
        have : Filter.Tendsto (fun lam : ℝ => (1 - lam) * eig i + lam * cA) (𝓝 (0:ℝ))
            (𝓝 ((1 - 0) * eig i + 0 * cA)) :=
          (by fun_prop : Continuous fun lam : ℝ => (1 - lam) * eig i + lam * cA).tendsto 0
        simpa using this
      exact ((Real.continuousAt_log (ne_of_gt heig_pos)).tendsto.comp hin).mono_left
        nhdsWithin_le_nhds
    have hdt : Filter.Tendsto (fun lam : ℝ => (1 - lam) * d i + lam * cB) (𝓝[>] (0:ℝ))
        (𝓝 (d i)) := by
      have : Filter.Tendsto (fun lam : ℝ => (1 - lam) * d i + lam * cB) (𝓝 (0:ℝ))
          (𝓝 ((1 - 0) * d i + 0 * cB)) :=
        (by fun_prop : Continuous fun lam : ℝ => (1 - lam) * d i + lam * cB).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    exact hlogt.mul hdt

omit [Nontrivial ℋ] in
/-- Tr of a nonneg operator is real. -/
lemma tr_eq_re {τ : L ℋ} (hτ : 0 ≤ τ) : Tr τ = ((Tr τ).re : ℂ) := by
  have hsym := ((LinearMap.nonneg_iff_isPositive τ).mp hτ).isSymmetric
  have h : Tr τ = ((∑ i, hsym.eigenvalues (rfl : Module.finrank ℂ ℋ = _) i : ℝ) : ℂ) :=
    hsym.trace_eq_sum_eigenvalues rfl
  apply Complex.ext
  · rw [Complex.ofReal_re]
  · rw [h]; simp

-- faithfulApprox.toFun in explicit form
lemma faithfulApprox_toFun_eq {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] (E : CPTP ℋ 𝒦)
    {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) {τ : L ℋ} (hτ : 0 ≤ τ) :
    (faithfulApprox E lam h0 h1).toFun τ
      = ((1 - lam : ℝ) : ℂ) • E.toFun τ
        + ((lam * ((Tr τ).re / (Module.finrank ℂ 𝒦 : ℝ)) : ℝ) : ℂ) • (1 : L 𝒦) := by
  have hdepol : ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun τ
      = ((lam * ((Tr τ).re / (Module.finrank ℂ 𝒦 : ℝ)) : ℝ) : ℂ) • (1 : L 𝒦) := by
    change ((lam : ℝ) : ℂ) • ((Tr τ / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)) = _
    rw [smul_smul]
    congr 1
    nth_rewrite 1 [tr_eq_re hτ]
    push_cast
    ring
  change ((1 - lam : ℝ) : ℂ) • E.toFun τ + ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun τ = _
  rw [hdepol]

theorem tendsto_umegakiNorm_faithful_real {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] (E : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0) (hsupp : suppLE ρ σ) :
    Filter.Tendsto
      (fun lam : ℝ =>
        umegakiNorm (((1 - lam : ℝ) : ℂ) • E.toFun ρ
            + ((lam * ((Tr ρ).re / (Module.finrank ℂ 𝒦 : ℝ)) : ℝ) : ℂ) • 1)
          (((1 - lam : ℝ) : ℂ) • E.toFun σ
            + ((lam * ((Tr σ).re / (Module.finrank ℂ 𝒦 : ℝ)) : ℝ) : ℂ) • 1))
      (𝓝[>] (0:ℝ)) (𝓝 (umegakiNorm (E.toFun ρ) (E.toFun σ))) := by
  have hEρ : (0 : L 𝒦) ≤ E.toFun ρ := map_nonneg E.toCompletelyPositiveMap hρ
  have hEσ : (0 : L 𝒦) ≤ E.toFun σ := map_nonneg E.toCompletelyPositiveMap hσ
  have hEsupp : suppLE (E.toFun ρ) (E.toFun σ) := suppLE_of_CPTP E hρ hσ hsupp
  have hEρ0 : E.toFun ρ ≠ 0 := CPTP_toFun_ne_zero E hρ hρ0
  have hσ0 : σ ≠ 0 := by
    rintro rfl; apply hρ0
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply]
    exact LinearMap.mem_ker.mp (hsupp (LinearMap.mem_ker.mpr (by simp)))
  have hd_pos : (0 : ℝ) < (Module.finrank ℂ 𝒦 : ℝ) := by exact_mod_cast Module.finrank_pos
  have hcρ : 0 < (Tr ρ).re / (Module.finrank ℂ 𝒦 : ℝ) :=
    div_pos (trace_re_pos_of_ne_zero hρ hρ0) hd_pos
  have hcσ : 0 < (Tr σ).re / (Module.finrank ℂ 𝒦 : ℝ) :=
    div_pos (trace_re_pos_of_ne_zero hσ hσ0) hd_pos
  set cρ := (Tr ρ).re / (Module.finrank ℂ 𝒦 : ℝ) with hcρ_def
  set cσ := (Tr σ).re / (Module.finrank ℂ 𝒦 : ℝ) with hcσ_def
  have hxlogx := tendsto_tr_faithful_cross hEρ hEρ (le_refl _) (cA := cρ) (cB := cρ) hcρ
  have hcross := tendsto_tr_faithful_cross hEσ hEρ hEsupp (cA := cσ) (cB := cρ) hcσ
  have hden : Filter.Tendsto
      (fun lam : ℝ => (Tr (((1 - lam : ℝ) : ℂ) • E.toFun ρ + ((lam * cρ : ℝ) : ℂ) • 1)).re)
      (𝓝[>] (0:ℝ)) (𝓝 (Tr (E.toFun ρ)).re) := by
    have key : (Tr (E.toFun ρ)).re
        = (Tr (((1 - (0:ℝ) : ℝ) : ℂ) • E.toFun ρ + (((0:ℝ) * cρ : ℝ) : ℂ) • 1)).re := by simp
    rw [key]
    exact ((QuantumState.continuous_re_trace.comp
      (by fun_prop : Continuous fun lam : ℝ =>
        ((1 - lam : ℝ) : ℂ) • E.toFun ρ + ((lam * cρ : ℝ) : ℂ) • 1)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have hnum : Filter.Tendsto
      (fun lam : ℝ => (Tr ((((1 - lam : ℝ) : ℂ) • E.toFun ρ + ((lam * cρ : ℝ) : ℂ) • 1) *
          (CFC.log (((1 - lam : ℝ) : ℂ) • E.toFun ρ + ((lam * cρ : ℝ) : ℂ) • 1)
            - CFC.log (((1 - lam : ℝ) : ℂ) • E.toFun σ + ((lam * cσ : ℝ) : ℂ) • 1)))).re)
      (𝓝[>] (0:ℝ))
      (𝓝 ((Tr (E.toFun ρ * (CFC.log (E.toFun ρ) - CFC.log (E.toFun σ)))).re)) := by
    have heqf : (fun lam : ℝ => (Tr ((((1 - lam : ℝ) : ℂ) • E.toFun ρ + ((lam * cρ : ℝ) : ℂ) • 1) *
          (CFC.log (((1 - lam : ℝ) : ℂ) • E.toFun ρ + ((lam * cρ : ℝ) : ℂ) • 1)
            - CFC.log (((1 - lam : ℝ) : ℂ) • E.toFun σ + ((lam * cσ : ℝ) : ℂ) • 1)))).re)
        = (fun lam : ℝ =>
            (Tr ((((1 - lam : ℝ) : ℂ) • E.toFun ρ + ((lam * cρ : ℝ) : ℂ) • 1) *
              CFC.log (((1 - lam : ℝ) : ℂ) • E.toFun ρ + ((lam * cρ : ℝ) : ℂ) • 1))).re
            - (Tr ((((1 - lam : ℝ) : ℂ) • E.toFun ρ + ((lam * cρ : ℝ) : ℂ) • 1) *
              CFC.log (((1 - lam : ℝ) : ℂ) • E.toFun σ + ((lam * cσ : ℝ) : ℂ) • 1))).re) := by
      funext lam; rw [mul_sub, map_sub, Complex.sub_re]
    rw [heqf, show (Tr (E.toFun ρ * (CFC.log (E.toFun ρ) - CFC.log (E.toFun σ)))).re
          = (Tr (E.toFun ρ * CFC.log (E.toFun ρ))).re - (Tr (E.toFun ρ * CFC.log (E.toFun σ))).re
          from by rw [mul_sub, map_sub, Complex.sub_re]]
    exact hxlogx.sub hcross
  have hden0 : (Tr (E.toFun ρ)).re ≠ 0 := ne_of_gt (trace_re_pos_of_ne_zero hEρ hEρ0)
  simpa only [umegakiNorm] using hnum.div hden hden0

theorem tendsto_umegakiNorm_faithful {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] (E : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0) (hsupp : suppLE ρ σ) :
    Filter.Tendsto
      (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        umegakiNorm ((faithfulApprox E l.val l.2.1.le l.2.2).toFun ρ)
          ((faithfulApprox E l.val l.2.1.le l.2.2).toFun σ))
      (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (𝓝[>] (0:ℝ)))
      (𝓝 (umegakiNorm (E.toFun ρ) (E.toFun σ))) := by
  have heq : (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        umegakiNorm ((faithfulApprox E l.val l.2.1.le l.2.2).toFun ρ)
          ((faithfulApprox E l.val l.2.1.le l.2.2).toFun σ))
      = (fun lam : ℝ =>
          umegakiNorm (((1 - lam : ℝ) : ℂ) • E.toFun ρ
              + ((lam * ((Tr ρ).re / (Module.finrank ℂ 𝒦 : ℝ)) : ℝ) : ℂ) • 1)
            (((1 - lam : ℝ) : ℂ) • E.toFun σ
              + ((lam * ((Tr σ).re / (Module.finrank ℂ 𝒦 : ℝ)) : ℝ) : ℂ) • 1))
        ∘ (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) := by
    funext l
    simp only [Function.comp_apply,
      faithfulApprox_toFun_eq E l.2.1.le l.2.2 hρ, faithfulApprox_toFun_eq E l.2.1.le l.2.2 hσ]
  rw [heq]
  exact (tendsto_umegakiNorm_faithful_real E hρ hσ hρ0 hsupp).comp Filter.tendsto_comap

/-- **Core non-negative DPI for `umegakiNorm`** (`supp ρ ⊆ supp σ`): assembled from
    `umegakiNorm_faithfulApprox_le` (each faithful `F_λ` decreases `umegakiNorm`) and the
    faithful limit `tendsto_umegakiNorm_faithful`. -/
theorem umegakiNorm_monotone_nn
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] (E : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hsupp : suppLE ρ σ) :
    umegakiNorm (E.toFun ρ) (E.toFun σ) ≤ umegakiNorm ρ σ := by
  by_cases hρ0 : ρ = 0
  · subst hρ0
    rw [show E.toFun 0 = 0 from map_zero E.toCompletelyPositiveMap.toLinearMap]
    simp only [umegakiNorm, zero_mul, map_zero, Complex.zero_re, zero_div, le_refl]
  · have step1 : ∀ (l : {l : ℝ // 0 < l ∧ l ≤ 1}),
        umegakiNorm ((faithfulApprox E l.val l.2.1.le l.2.2).toFun ρ)
          ((faithfulApprox E l.val l.2.1.le l.2.2).toFun σ) ≤ umegakiNorm ρ σ :=
      fun l => umegakiNorm_faithfulApprox_le E hρ hσ hρ0 hsupp l.2.1 l.2.2
    haveI hNeBot : (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val)
        (𝓝[>] (0:ℝ))).NeBot := by
      refine Filter.comap_neBot fun t ht => ?_
      obtain ⟨U, hU_open, hU0, hU_sub⟩ := mem_nhdsWithin.mp ht
      obtain ⟨δ, hδ_pos, hball⟩ := Metric.mem_nhds_iff.mp (hU_open.mem_nhds hU0)
      have hx_pos : (0 : ℝ) < min (δ / 2) 1 := lt_min (by positivity) one_pos
      refine ⟨⟨min (δ / 2) 1, hx_pos, min_le_right _ _⟩, ?_⟩
      apply hU_sub
      refine ⟨hball ?_, hx_pos⟩
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx_pos]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    exact le_of_tendsto (tendsto_umegakiNorm_faithful E hρ hσ hρ0 hsupp)
      (Filter.Eventually.of_forall step1)

/-- **Data-processing for the Umegaki relative entropy on non-negative operators.**
    Off-support the right-hand side is `⊤` (trivial); on-support it reduces to the
    real-valued core DPI `umegakiNorm_monotone_nn`. -/
theorem umegakiRelEntropyNN_monotone
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] (E : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    umegakiRelEntropyNN (E.toFun ρ) (E.toFun σ) ≤ umegakiRelEntropyNN ρ σ := by
  by_cases hsupp : suppLE ρ σ
  · -- support holds: both sides are real, reduce to the core DPI
    have hEρ : (0 : L 𝒦) ≤ E.toFun ρ := map_nonneg E.toCompletelyPositiveMap hρ
    have hEσ : (0 : L 𝒦) ≤ E.toFun σ := map_nonneg E.toCompletelyPositiveMap hσ
    have hEsupp : suppLE (E.toFun ρ) (E.toFun σ) := suppLE_of_CPTP E hρ hσ hsupp
    rw [show umegakiRelEntropyNN (E.toFun ρ) (E.toFun σ)
          = ((umegakiNorm (E.toFun ρ) (E.toFun σ) : ℝ) : EReal) from by
        unfold umegakiRelEntropyNN; rw [if_pos hEsupp],
      show umegakiRelEntropyNN ρ σ = ((umegakiNorm ρ σ : ℝ) : EReal) from by
        unfold umegakiRelEntropyNN; rw [if_pos hsupp],
      EReal.coe_le_coe_iff]
    exact umegakiNorm_monotone_nn E hρ hσ hsupp
  · -- support fails: the right-hand side is `⊤`
    have h_RHS : umegakiRelEntropyNN ρ σ = (⊤ : EReal) := by
      unfold umegakiRelEntropyNN; rw [if_neg hsupp]
    rw [h_RHS]; exact le_top

/-! ### α = ∞ as the `α → ∞` limit (Frank–Lieb limiting argument)

Following the same limiting strategy as the `α = 1` case, we show the sandwiched
Rényi divergence converges, as `α → ∞`, to the max-relative entropy
`log ‖σ^{-1/2} ρ σ^{-1/2}‖`, and re-derive its data-processing inequality from the
finite-`α` monotonicity (`sandwichedRenyiDiv_monotone`) by passing to the limit.

The convergence rests on the elementary squeeze `‖B‖^α ≤ Tr(B^α) ≤ d·‖B‖^α` for a
non-negative operator `B` (with `d = dim ℋ`), i.e. the `ℓ^α → ℓ^∞` collapse of the
spectrum. -/

/-- For a non-negative operator, the operator norm (largest eigenvalue) is bounded
    by the (real) trace (the sum of the eigenvalues). -/
lemma norm_le_re_trace {C : L ℋ} (hC : 0 ≤ C) : ‖C‖ ≤ (Tr C).re := by
  classical
  have hpos : C.IsPositive := (LinearMap.nonneg_iff_isPositive C).mp hC
  have hsym : C.IsSymmetric := hpos.isSymmetric
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  set b := hsym.eigenvectorBasis hn with hb
  set eig := hsym.eigenvalues hn with heig
  have h_eig_nn : ∀ i, 0 ≤ eig i := fun i => hpos.nonneg_eigenvalues hn i
  have h_eig_apply : ∀ i, C (b i) = ((eig i : ℝ) : ℂ) • b i := hsym.apply_eigenvectorBasis hn
  have htr : (Tr C).re = ∑ i, eig i := hsym.re_trace_eq_sum_eigenvalues hn
  -- `‖C‖` is attained as an eigenvalue.
  have hmemℝ : ‖C‖ ∈ spectrum ℝ C := CStarAlgebra.norm_mem_spectrum_of_nonneg hC
  have hmemℂ : (‖C‖ : ℂ) ∈ spectrum ℂ C := by
    have h := hmemℝ; rw [← spectrum.preimage_algebraMap ℂ] at h; simpa using h
  have hev : Module.End.HasEigenvalue C (‖C‖ : ℂ) :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hmemℂ
  obtain ⟨w, hw⟩ := hev.exists_hasEigenvector
  have hCw : C w = (‖C‖ : ℂ) • w := Module.End.mem_eigenspace_iff.mp hw.1
  have hw_ne : w ≠ 0 := hw.2
  obtain ⟨j, hcj⟩ : ∃ j, inner ℂ (b j) w ≠ (0 : ℂ) := by
    by_contra h; push_neg at h
    apply hw_ne
    have hrep : w = ∑ i, inner ℂ (b i) w • b i := (b.sum_repr' w).symm
    rw [hrep]; simp [h]
  have hkey : (eig j : ℂ) * inner ℂ (b j) w = (‖C‖ : ℂ) * inner ℂ (b j) w := by
    have h1 : inner ℂ (b j) (C w) = (‖C‖ : ℂ) * inner ℂ (b j) w := by rw [hCw, inner_smul_right]
    have h2 : inner ℂ (b j) (C w) = (eig j : ℂ) * inner ℂ (b j) w := by
      rw [show inner ℂ (b j) (C w) = inner ℂ (C (b j)) w from (hsym (b j) w).symm,
        h_eig_apply j, inner_smul_left, Complex.conj_ofReal]
    rw [← h1, h2]
  have hej : eig j = ‖C‖ := by exact_mod_cast mul_right_cancel₀ hcj hkey
  rw [htr, ← hej]
  exact Finset.single_le_sum (fun i _ => h_eig_nn i) (Finset.mem_univ j)
end Umegaki
end SandwichedRenyiRelativeEntropy


