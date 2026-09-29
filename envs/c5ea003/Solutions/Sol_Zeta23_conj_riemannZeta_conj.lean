-- Prove2me | solution 1 for Zeta23_conj_riemannZeta_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:39:53.09646+00:00
-- url     : https://prove2.me/submissions/29b146eb-5773-40e4-85f9-3f179fa7ecb8

import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Theorems.Thm_Zeta23_conj_riemannZeta_conj_aux1

-- from Zeta23.FromPNTPlus.ZetaConj
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/ZetaConj.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
blueprint_comment blocks, @[blueprint ...] attributes).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open scoped Complex ComplexConjugate


/- v4.30 port: Mathlib c5ea003 predates `riemannZeta_conj`, so we restore the local proof
from the v4.30-era PrimeNumberTheoremAnd/ZetaConj.lean (commit f55e855). -/






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
        exact Zeta23_conj_riemannZeta_conj_aux1 s hs
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
