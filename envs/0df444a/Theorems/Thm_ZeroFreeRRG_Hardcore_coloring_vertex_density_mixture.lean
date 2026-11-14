-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_vertex_density_mixture
-- name    : ZeroFreeRRG.Hardcore.coloring_vertex_density_mixture
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:35:26.252204+00:00
-- url     : https://prove2.me/theorems/2ee82c1f-e97e-4761-8216-a90ab0a11f31
-- title:
--   Coloring vertex factor as a latent-color density mixture
-- statement:
--   Fix $q\ge3$ and $d\ge0$. For messages whose coordinates each sum to one, the coloring vertex factor equals the uniform average, over colors $i$, of the product over observations $j$ of the densities $q(1-x_{j,i})/(q-1)$. This identifies the vertex factor with the joint density in the exchangeable latent-color construction of Lemma 4.27.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.27, printed p. 34.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical BigOperators

namespace ZeroFreeRRG.Hardcore
theorem coloring_vertex_density_mixture (q d : ℕ) (hq : 3 ≤ q) (xs : Fin d → Fin q → ℝ)
    (hs : ∀ j, (∑ i, xs j i) = 1) :
    vertexFactor (.potts q) 0 d xs =
      (q:ℝ)⁻¹ * ∑ i : Fin q, ∏ j : Fin d, (q:ℝ)*(1-xs j i)/((q:ℝ)-1) := by sorry
end ZeroFreeRRG.Hardcore
