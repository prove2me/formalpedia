-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_ordered_excess_measure_coupling
-- name    : ZeroFreeRRG.Hardcore.ordered_excess_measure_coupling
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:17:05.063286+00:00
-- url     : https://prove2.me/theorems/1456835c-259e-4d04-bf4f-d5db10aa7a56
-- title:
--   Explicit monotone coupling of ordered excess measures
-- statement:
--   Let $C,L,H$ be finite measures on $\mathbb R$, with $L$ and $H$ having the same nonzero mass $m$. Assume $L$ is supported on $(-\infty,t]$ and $H$ on $[t,\infty)$. The measure $\pi=\mathrm{diag}_{*}C+m^{-1}(L\otimes H)$ has first marginal $C+L$, second marginal $C+H$, and is supported on pairs $(x,y)$ with $x\le y$. This is an explicit coupling construction for the size-bias comparison in Lemma 4.17.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed p. 30.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

namespace ZeroFreeRRG.Hardcore
theorem ordered_excess_measure_coupling (common low high : Measure ℝ)
    [IsFiniteMeasure common] [IsFiniteMeasure low] [IsFiniteMeasure high]
    (hmass : low univ = high univ) (h0 : low univ ≠ 0) (t : ℝ)
    (hlow : ∀ᵐ x ∂low, x ≤ t) (hhigh : ∀ᵐ y ∂high, t ≤ y) :
    let π : Measure (ℝ × ℝ) := Measure.map (fun x => (x,x)) common +
      (low univ)⁻¹ • (low.prod high)
    Measure.map Prod.fst π = common+low ∧ Measure.map Prod.snd π = common+high ∧
      (∀ᵐ p ∂π, p.1 ≤ p.2) := by sorry
end ZeroFreeRRG.Hardcore
