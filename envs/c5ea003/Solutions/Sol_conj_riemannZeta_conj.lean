-- Prove2me | solution 1 for conj_riemannZeta_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T19:37:54.152112+00:00
-- url     : https://prove2.me/submissions/eb6f6bd6-6a2a-44f3-865e-b2e91a9043ab

import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Theorems.Thm_conj_riemannZeta_conj_aux1

open scoped Complex ComplexConjugate

theorem solution (s : ℂ) : conj (riemannZeta (conj s)) = riemannZeta s := by
  by_cases hs1 : s = 1
  · subst hs1
    rw [map_one, Complex.conj_eq_iff_real, riemannZeta_one]
    use (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2
    rw [show (4 * ↑Real.pi : ℂ) = ↑(4 * Real.pi) from by push_cast; ring,
      ← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 4 * Real.pi)]
    push_cast
    ring
  · let U : Set ℂ := {1}ᶜ
    let g := fun s ↦ conj (riemannZeta (conj s))
    suffices Set.EqOn g riemannZeta U by
      apply this
      rwa [Set.mem_compl_singleton_iff]
    apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ) (z₀ := 2)
    · simp [U]
    · rw [Filter.eventuallyEq_iff_exists_mem]
      set V := Complex.re ⁻¹' (Set.Ioi 1)
      use V
      constructor
      · have Vopen : IsOpen V := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
        exact Vopen.mem_nhds (by simp [V])
      · intro s hs
        exact conj_riemannZeta_conj_aux1 s hs
    · refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
      intro s₁ hs₁
      have hs₁' : conj s₁ ≠ 1 :=
        (map_ne_one_iff (starRingEnd ℂ) (RingHom.injective (starRingEnd ℂ))).mpr hs₁
      convert (HasDerivAt.conj_conj
        (differentiableAt_riemannZeta hs₁').hasDerivAt).differentiableAt.differentiableWithinAt
        (s := U)
      rw [Complex.conj_conj]
    · refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
      intro s₁ hs₁
      exact (differentiableAt_riemannZeta hs₁).differentiableWithinAt
    · exact (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected

