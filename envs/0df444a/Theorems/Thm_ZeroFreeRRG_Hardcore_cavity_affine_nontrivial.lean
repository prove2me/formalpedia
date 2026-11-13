-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_cavity_affine_nontrivial
-- name    : ZeroFreeRRG.Hardcore.cavity_affine_nontrivial
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:25:56.972098+00:00
-- url     : https://prove2.me/theorems/b8b15ab7-4152-4571-b28d-9ede29798eb9
-- title:
--   Affine contraction preserves nonconstant cavity laws
-- statement:
--   Let $\nu$ be a nonconstant admissible cavity law with mean $\pi(t)$, let $r$ be a probability vector, and let $c\in(0,1]$. If $\pi(t')=(1-c)r+c\pi(t)$, then the law $\nu'$ of $(1-c)r+c\mu$ for $\mu\sim\nu$ is admissible with mean $\pi(t')$ and is also nonconstant:
--
--   $$\nu'\in\mathcal P_{\pi(t')}\setminus\{\delta_{\pi(t')}\}.$$
--
--   This formalizes the admissibility and nontriviality of the affine transformations used in the Bethe comparison of Lemma 4.17.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed pp. 30–31; generalized law-transport step.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical
open MeasureTheory

namespace ZeroFreeRRG.Hardcore
/-- Nonzero affine contractions preserve nonconstant cavity laws. -/
theorem cavity_affine_nontrivial (m : Model) (t t' : ℝ) (ν : ProbabilityMeasure (m.Spin → ℝ))
    (hν : ν ∈ cavityLaws m t) (r : m.Spin → ℝ) (hr : r ∈ stdSimplex ℝ m.Spin)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hc : c ≠ 0)
    (hmean : ∀ i, m.pi t' i = (1-c)*r i+c*m.pi t i) (hne : ν ≠ diracPi m t) :
    ∃ ν' ∈ cavityLaws m t', ν' ≠ diracPi m t' ∧
      (ν' : Measure (m.Spin → ℝ)) =
      Measure.map (fun μ : m.Spin → ℝ => fun i => (1-c)*r i+c*μ i)
        (ν : Measure (m.Spin → ℝ)) := by sorry
end ZeroFreeRRG.Hardcore
