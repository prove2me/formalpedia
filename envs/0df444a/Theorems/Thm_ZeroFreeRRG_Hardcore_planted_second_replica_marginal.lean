-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_planted_second_replica_marginal
-- name    : ZeroFreeRRG.Hardcore.planted_second_replica_marginal
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:07:00.176307+00:00
-- url     : https://prove2.me/theorems/6a5e0a87-6238-4e97-b534-e20949db28da
-- title:
--   The second Gibbs replica has the planted marginal
-- statement:
--   Under the planted joint law with an independent Gibbs replica and an independent reveal set, averaging any function of the second replica and reveal set gives the original planted reveal expectation.
-- source:
--   Auxiliary identity for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.planted_second_replica_marginal (m : Model) (hm : m.Valid) (t s : ℝ) (ht : m.PosParam t) (d n : ℕ)
    (f : Matching n d → (Fin n → m.Spin) → Finset (Fin n) → ℝ) :
    (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
      planted m t M σ * gibbs m t M σ' * revealProb s U * f M σ' U) =
        plantedPinnedE m t s d n f := by sorry
