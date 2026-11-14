-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_planted_replica_exchange
-- name    : ZeroFreeRRG.Hardcore.planted_replica_exchange
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:05:07.475195+00:00
-- url     : https://prove2.me/theorems/2eeee1fa-f92e-470e-9c61-fa3abb66e9c5
-- title:
--   Exchangeability of planted and Gibbs replicas
-- statement:
--   For every configuration-model matching and two spin configurations, the product of the planted weight of the first and the Gibbs weight of the second is unchanged when the two configurations are swapped.
-- source:
--   Auxiliary probabilistic identity for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, §4.3 and p. 39, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.planted_replica_exchange (m : Model) (t : ℝ) (d n : ℕ)
    (M : Matching n d) (σ σ' : Fin n → m.Spin) :
    planted m t M σ * gibbs m t M σ' = planted m t M σ' * gibbs m t M σ := by sorry
