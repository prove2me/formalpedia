-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_replica_reveal_density_bound
-- name    : ZeroFreeRRG.Hardcore.replica_reveal_density_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:11:42.65499+00:00
-- url     : https://prove2.me/theorems/74e342c2-3c98-46d7-b090-6a1b4d34ebde
-- title:
--   Revealed two-replica density bound
-- statement:
--   If the two revealed Gibbs marginals and all spin marginal probabilities are positive and the sum of pinned log-likelihoods is at most B, their joint revealed Gibbs mass is at most exp(B) times the corresponding product-prior mass.
-- source:
--   Auxiliary revealed-density identity in Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, pp. 39–40, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.replica_reveal_density_bound (m : Model) (t : ℝ) (d n : ℕ) (M : Matching n d)
    (σ σ' : Fin n → m.Spin) (U : Finset (Fin n)) (B : ℝ)
    (hπ : ∀ a, 0 < m.pi t a)
    (hG : 0 < gibbsMarg m t M σ U) (hG' : 0 < gibbsMarg m t M σ' U)
    (hgood : pinnedLL m t M σ U + pinnedLL m t M σ' U ≤ B) :
    gibbsMarg m t M σ U * gibbsMarg m t M σ' U ≤
      Real.exp B * ((∏ v ∈ U, m.pi t (σ v)) * (∏ v ∈ U, m.pi t (σ' v))) := by sorry
