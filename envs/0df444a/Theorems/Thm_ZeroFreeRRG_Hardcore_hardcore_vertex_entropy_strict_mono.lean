-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_vertex_entropy_strict_mono
-- name    : ZeroFreeRRG.Hardcore.hardcore_vertex_entropy_strict_mono
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:17:25.326243+00:00
-- url     : https://prove2.me/theorems/8a0e773e-215a-47ec-be9a-97e2964717b9
-- title:
--   Strict monotonicity of hardcore vertex entropy
-- statement:
--   For $d\ge2$ and a nontrivial mean-zero cavity law supported on $[-1,1]$, the expected hardcore vertex entropy $\mathbb E[V_\theta\log V_\theta]$ is strictly increasing on $0<\theta<1$, with $V_\theta$ as displayed in the formal statement.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, pp. 29–31.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.hardcore_vertex_entropy_strict_mono (d : ℕ) (hd : 2 ≤ d) (η : Measure ℝ) [IsProbabilityMeasure η]
    (hb : ∀ᵐ h ∂η, -1 ≤ h ∧ h ≤ 1)
    (hint : Integrable (fun h : ℝ => h) η)
    (hmean : (∫ h : ℝ, h ∂η) = 0) (hn : ¬(∀ᵐ h ∂η, h=0)) :
    StrictMonoOn (fun t : ℝ => ∫ hs : Fin d → ℝ,
      let V := ((∏ i, (1+t*hs i)) + t*(∏ i, (1-hs i)))/(1+t)
      V * Real.log V ∂(Measure.pi fun _ : Fin d => η)) (Ioo 0 1) := by sorry
