-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_pinned_likelihood_density
-- name    : ZeroFreeRRG.Hardcore.pinned_likelihood_density
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:11:28.625479+00:00
-- url     : https://prove2.me/theorems/a5caf46f-3d36-4501-ac5f-6711ff8cf630
-- title:
--   Pinned likelihood equals the revealed marginal density
-- statement:
--   If all spin marginal probabilities and the Gibbs marginal of a revealed pattern are positive, the exponential of the pinned log-likelihood equals the Gibbs probability of the revealed pattern divided by its product-prior probability.
-- source:
--   Auxiliary revealed-density identity in Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, pp. 39–40, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.pinned_likelihood_density (m : Model) (t : ℝ) (d n : ℕ) (M : Matching n d)
    (σ : Fin n → m.Spin) (U : Finset (Fin n))
    (hπ : ∀ a, 0 < m.pi t a) (hG : 0 < gibbsMarg m t M σ U) :
    Real.exp (pinnedLL m t M σ U) =
      gibbsMarg m t M σ U / ∏ v ∈ U, m.pi t (σ v) := by sorry
