-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_cavity_affine_transport
-- name    : ZeroFreeRRG.Hardcore.cavity_affine_transport
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:24:08.888203+00:00
-- url     : https://prove2.me/theorems/584397a4-4ccb-4b64-a01e-cc1ba8448299
-- title:
--   Affine transport of cavity laws
-- statement:
--   Let $\nu$ be an admissible cavity law with barycenter $\pi(t)$, let $r$ be a probability vector, and let $c\in[0,1]$. Suppose the new model marginal is
--
--   $$\pi(t')=(1-c)r+c\pi(t).$$
--
--   Then the law obtained by mapping every message $\mu$ to $(1-c)r+c\mu$ is an admissible cavity law with barycenter $\pi(t')$. This generalizes the affine message transformations used to compare Bethe functionals in the proof of Lemma 4.17; it establishes admissibility and the new mean, not the Bethe-functional inequality.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed pp. 30–31; generalized admissibility and mean step.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical
open MeasureTheory

namespace ZeroFreeRRG.Hardcore
/-- Affine contraction of messages transports admissible cavity laws and their barycenters. -/
theorem cavity_affine_transport (m : Model) (t t' : ℝ) (ν : ProbabilityMeasure (m.Spin → ℝ))
    (hν : ν ∈ cavityLaws m t) (r : m.Spin → ℝ) (hr : r ∈ stdSimplex ℝ m.Spin)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hmean : ∀ i, m.pi t' i = (1-c)*r i+c*m.pi t i) :
    ∃ ν' ∈ cavityLaws m t', (ν' : Measure (m.Spin → ℝ)) =
      Measure.map (fun μ : m.Spin → ℝ => fun i => (1-c)*r i+c*μ i)
        (ν : Measure (m.Spin → ℝ)) := by sorry
end ZeroFreeRRG.Hardcore
