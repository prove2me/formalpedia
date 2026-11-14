-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_replica_reveal_density_bound_nonnegative
-- name    : ZeroFreeRRG.Hardcore.replica_reveal_density_bound_nonnegative
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:12:37.571636+00:00
-- url     : https://prove2.me/theorems/005e4e26-1370-41b5-80d9-238b2def5133
-- title:
--   Revealed two-replica density bound with zero marginals
-- statement:
--   If the Gibbs weights are nonnegative, the spin marginal probabilities are positive, and the sum of pinned log-likelihoods is at most $B$, then the product of the two revealed Gibbs marginals is at most $e^B$ times their product-prior mass. The conclusion includes revealed patterns with zero Gibbs marginal.
-- source:
--   Auxiliary revealed-density bound in Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, pp. 39–40, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.replica_reveal_density_bound_nonnegative (m : Model) (t : ℝ) (d n : ℕ) (M : Matching n d)
    (σ σ' : Fin n → m.Spin) (U : Finset (Fin n)) (B : ℝ)
    (hπ : ∀ a, 0 < m.pi t a) (hnonneg : ∀ τ, 0 ≤ gibbs m t M τ)
    (hgood : pinnedLL m t M σ U + pinnedLL m t M σ' U ≤ B) :
    gibbsMarg m t M σ U * gibbsMarg m t M σ' U ≤
      Real.exp B * ((∏ v ∈ U, m.pi t (σ v)) * (∏ v ∈ U, m.pi t (σ' v))) := by sorry
