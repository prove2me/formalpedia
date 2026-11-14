-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_centered_vertex_expectation
-- name    : ZeroFreeRRG.Hardcore.hardcore_centered_vertex_expectation
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:20:05.181211+00:00
-- url     : https://prove2.me/theorems/318d6de7-6de9-4db2-80f7-7b65d440d61f
-- title:
--   Hardcore vertex entropy in centered cavity coordinates
-- statement:
--   For a hardcore cavity law $\nu$ at $0<\alpha<1/2$, let $\eta$ be its image under $h=(\mu_1-\alpha)/(1-\alpha)$. The vertex-entropy expectation in the Bethe functional equals $\mathbb E_{\eta^{\otimes d}}[V\log V]$, with the centered vertex factor $V$ displayed in the formal statement.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, equation (25), pp. 29–31.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.hardcore_centered_vertex_expectation (d : ℕ) (α : ℝ) (ha : 0 < α) (ha1 : α < 1/2)
    (ν : ProbabilityMeasure (Fin 2 → ℝ)) (hν : ν ∈ cavityLaws .hardcore α) :
    let η := Measure.map (fun x : Fin 2 → ℝ => (x 1-α)/(1-α)) (ν : Measure (Fin 2 → ℝ))
    (∫ xs : Fin d → Fin 2 → ℝ, xlogx (vertexFactor .hardcore α d xs)
      ∂(Measure.pi fun _ : Fin d => (ν : Measure (Fin 2 → ℝ)))) =
    ∫ hs : Fin d → ℝ,
      let V := ((∏ i, (1+(α/(1-α))*hs i)) + (α/(1-α))*(∏ i, (1-hs i)))/(1+α/(1-α))
      V * Real.log V ∂(Measure.pi fun _ : Fin d => η) := by sorry
