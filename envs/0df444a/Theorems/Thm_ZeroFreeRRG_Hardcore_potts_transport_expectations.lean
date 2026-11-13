-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_transport_expectations
-- name    : ZeroFreeRRG.Hardcore.potts_transport_expectations
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:44:42.675208+00:00
-- url     : https://prove2.me/theorems/243c49aa-16c3-400f-b9b6-86e7288566d7
-- title:
--   Potts cavity-factor expectations under affine transport
-- statement:
--   Suppose $q\ge2$, $\beta,\beta'\ge0$, and $c\kappa_{\beta'}=\kappa_\beta$. Let $\nu$ be a Potts cavity law at $\beta$ and let $\nu'$ be its pushforward by $\mu\mapsto(1-c)U_q+c\mu$. For independent messages drawn from the corresponding laws, the vertex entropy expectation is unchanged and the edge entropy expectation transforms as
--
--   $$\mathbb E_{\nu'^{\otimes2}}[E_{\beta'}\log E_{\beta'}]=\mathbb E_{\nu^{\otimes2}}[(1-c+cE_\beta)\log(1-c+cE_\beta)].$$
--
--   This lifts the pointwise factor identities to the product-law expectations used in the Bethe comparison of Lemma 4.17.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed pp. 30–31, immediately before equation (27).

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical BigOperators
open MeasureTheory

namespace ZeroFreeRRG.Hardcore
theorem potts_transport_expectations (q d : ℕ) (hq : 2 ≤ q) (β β' c : ℝ)
    (hb : 0 ≤ β) (hb' : 0 ≤ β')
    (hk : c*((β'-1)/((q:ℝ)-1+β')) = (β-1)/((q:ℝ)-1+β))
    (ν ν' : ProbabilityMeasure (Fin q → ℝ)) (hν : ν ∈ cavityLaws (.potts q) β)
    (hmap : (ν' : Measure (Fin q → ℝ)) = Measure.map (fun μ : Fin q → ℝ => fun i => (1-c)*(q:ℝ)⁻¹+c*μ i) (ν : Measure (Fin q → ℝ))) :
    (∫ ys, xlogx (vertexFactor (.potts q) β' d ys)
      ∂(Measure.pi fun _ : Fin d => (ν' : Measure (Fin q → ℝ)))) =
    (∫ xs, xlogx (vertexFactor (.potts q) β d xs)
      ∂(Measure.pi fun _ : Fin d => (ν : Measure (Fin q → ℝ)))) ∧
    (∫ ys, xlogx (edgeFactor (.potts q) β' ys.1 ys.2)
      ∂((ν' : Measure (Fin q → ℝ)).prod (ν' : Measure (Fin q → ℝ)))) =
    (∫ xs, xlogx (1-c+c*edgeFactor (.potts q) β xs.1 xs.2)
      ∂((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ)))) := by sorry
end ZeroFreeRRG.Hardcore
