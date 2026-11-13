-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_affine_factors
-- name    : ZeroFreeRRG.Hardcore.potts_affine_factors
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:37:05.237713+00:00
-- url     : https://prove2.me/theorems/06d8ed9b-4747-4a02-ae4c-a21522db19b1
-- title:
--   Potts vertex and edge factors under matched contraction
-- statement:
--   Let $q\ge2$, $\beta,\beta'\ge0$, and let $c$ match the centered Potts eigenvalues by $c\kappa_{\beta'}=\kappa_\beta$, where $\kappa_\beta=(\beta-1)/(q-1+\beta)$. For every normalized collection of messages $\mu_1,\ldots,\mu_d$ and normalized messages $\mu,\nu$, define $\mu^c=(1-c)U_q+c\mu$. Then
--
--   $$V_{d,\beta'}(\mu_1^c,\ldots,\mu_d^c)=V_{d,\beta}(\mu_1,\ldots,\mu_d),\qquad E_{\beta'}(\mu^c,\nu^c)=1-c+cE_\beta(\mu,\nu).$$
--
--   These algebraic identities are the message-contraction step in the Potts comparison in Lemma 4.17. The statement needs only normalization of the messages, so it applies in particular to probability vectors.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed pp. 30–31, immediately before equation (27).

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical BigOperators

namespace ZeroFreeRRG.Hardcore
/-- The vertex and edge identities under matched Potts message contraction. -/
theorem potts_affine_factors (q d : ℕ) (hq : 2 ≤ q) (β β' c : ℝ)
    (hb : 0 ≤ β) (hb' : 0 ≤ β')
    (hk : c*((β'-1)/((q:ℝ)-1+β')) = (β-1)/((q:ℝ)-1+β))
    (μs : Fin d → Fin q → ℝ) (hμs : ∀ r, (∑ i, μs r i) = 1)
    (μ ν : Fin q → ℝ) (hμ : (∑ i, μ i) = 1) (hν : (∑ i, ν i) = 1) :
    vertexFactor (.potts q) β' d (fun r j => (1-c)*(q:ℝ)⁻¹+c*μs r j) =
      vertexFactor (.potts q) β d μs ∧
    edgeFactor (.potts q) β'
      (fun i => (1-c)*(q:ℝ)⁻¹+c*μ i) (fun i => (1-c)*(q:ℝ)⁻¹+c*ν i) =
      1-c+c*edgeFactor (.potts q) β μ ν := by sorry
end ZeroFreeRRG.Hardcore
