-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_contraction_data
-- name    : ZeroFreeRRG.Hardcore.potts_contraction_data
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:40:38.930298+00:00
-- url     : https://prove2.me/theorems/1fb66b22-0e60-4bb0-b9a9-4ffa770bec08
-- title:
--   Potts cavity contraction and factor identities
-- statement:
--   Fix $q\ge2$, $0\le\beta'<\beta<1$, and a cavity law $\nu$ at $\beta$. Put $c=\kappa_\beta/\kappa_{\beta'}$, where $\kappa_\beta=(\beta-1)/(q-1+\beta)$. Then $0<c<1$, and the law $\nu'$ obtained by contracting each message toward the uniform law $U_q$ by $c$ is admissible at $\beta'$. A nonconstant $\nu$ gives a nonconstant $\nu'$.
--
--   For normalized messages, the transformed vertex and edge factors satisfy
--
--   $$V_{d,\beta'}(\mu_1^c,\ldots,\mu_d^c)=V_{d,\beta}(\mu_1,\ldots,\mu_d),\qquad E_{\beta'}(\mu^c,\xi^c)=1-c+cE_\beta(\mu,\xi).$$
--
--   This assembles the deterministic law-transport and factor identities underlying the Potts comparison in Lemma 4.17; it does not yet prove the Bethe-functional inequality.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed pp. 30–31.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical BigOperators
open MeasureTheory

namespace ZeroFreeRRG.Hardcore
theorem potts_contraction_data (q d : ℕ) (hq : 2 ≤ q) (β β' : ℝ)
    (hb' : 0 ≤ β') (hlt : β' < β) (hb : β < 1)
    (ν : ProbabilityMeasure ((.potts q : Model).Spin → ℝ)) (hν : ν ∈ cavityLaws (.potts q) β) :
    let c := ((β-1)/((q:ℝ)-1+β)) / ((β'-1)/((q:ℝ)-1+β'))
    0 < c ∧ c < 1 ∧ ∃ ν' ∈ cavityLaws (.potts q) β',
      (ν ≠ diracPi (.potts q) β → ν' ≠ diracPi (.potts q) β') ∧
      (ν' : Measure ((.potts q : Model).Spin → ℝ)) =
        Measure.map (fun μ : ((.potts q : Model).Spin → ℝ) => fun i : (.potts q : Model).Spin => (1-c)*(q:ℝ)⁻¹+c*μ i)
          (ν : Measure ((.potts q : Model).Spin → ℝ)) ∧
      (∀ (μs : Fin d → Fin q → ℝ), (∀ r, (∑ i, μs r i) = 1) →
        vertexFactor (.potts q) β' d (fun r j => (1-c)*(q:ℝ)⁻¹+c*μs r j) =
          vertexFactor (.potts q) β d μs) ∧
      (∀ (μ ξ : Fin q → ℝ), (∑ i, μ i) = 1 → (∑ i, ξ i) = 1 →
        edgeFactor (.potts q) β'
          (fun i => (1-c)*(q:ℝ)⁻¹+c*μ i) (fun i => (1-c)*(q:ℝ)⁻¹+c*ξ i) =
          1-c+c*edgeFactor (.potts q) β μ ξ) := by sorry
end ZeroFreeRRG.Hardcore
