-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_replica_likelihood_union_bound
-- name    : ZeroFreeRRG.Hardcore.replica_likelihood_union_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:08:02.531214+00:00
-- url     : https://prove2.me/theorems/a7d156f0-359b-4aff-9d06-f7047f51523a
-- title:
--   Two-replica pinned likelihood union bound
-- statement:
--   For a planted configuration and an independent Gibbs replica, using the same independently sampled reveal set, the joint probability that their two pinned log-likelihoods sum to more than $2B$ is at most twice the single-replica planted probability that the pinned log-likelihood exceeds $B$.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.replica_likelihood_union_bound (m : Model) (hm : m.Valid) (t s : ℝ) (ht : m.PosParam t)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (d n : ℕ) (B : ℝ) :
    (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
      planted m t M σ * gibbs m t M σ' * revealProb s U *
        (if pinnedLL m t M σ U + pinnedLL m t M σ' U > 2*B then 1 else 0)) ≤
    2 * plantedPinnedE m t s d n (fun M σ U => if pinnedLL m t M σ U > B then 1 else 0) := by sorry
