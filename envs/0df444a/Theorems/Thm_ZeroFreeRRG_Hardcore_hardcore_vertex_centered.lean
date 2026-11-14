-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_vertex_centered
-- name    : ZeroFreeRRG.Hardcore.hardcore_vertex_centered
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:19:08.697235+00:00
-- url     : https://prove2.me/theorems/ea642371-350b-4f7d-9ed2-ffb33ded9a25
-- title:
--   Centered representation of the hardcore vertex factor
-- statement:
--   For hardcore messages with coordinates summing to one and $0<\alpha<1/2$, set $\theta=\alpha/(1-\alpha)$ and $h_i=(\mu_{i,1}-\alpha)/(1-\alpha)$. The vertex factor in the paper equals $$\frac{\prod_i(1+\theta h_i)+\theta\prod_i(1-h_i)}{1+\theta}.$$
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, equation (25), pp. 29–31.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
set_option autoImplicit false
open MeasureTheory ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.hardcore_vertex_centered (d : ℕ) (α : ℝ) (ha : 0 < α) (ha1 : α < 1/2)
    (xs : Fin d → Fin 2 → ℝ) (hs : ∀ i, ∑ a, xs i a = 1) :
    let θ := α/(1-α)
    let h := fun i => (xs i 1-α)/(1-α)
    vertexFactor .hardcore α d xs =
      ((∏ i, (1+θ*h i)) + θ*(∏ i, (1-h i)))/(1+θ) := by sorry
