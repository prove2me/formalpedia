-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_planted_first_replica_marginal
-- name    : ZeroFreeRRG.Hardcore.planted_first_replica_marginal
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:07:15.144643+00:00
-- url     : https://prove2.me/theorems/f50a63cc-9b49-45b0-87f1-6ee2aac5022e
-- title:
--   The first planted replica has the planted marginal
-- statement:
--   Under the planted joint law with an independent Gibbs replica and an independent reveal set, averaging any function of the first replica and reveal set gives the original planted reveal expectation.
-- source:
--   Auxiliary identity for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.planted_first_replica_marginal (m : Model) (hm : m.Valid) (t s : ℝ) (ht : m.PosParam t) (d n : ℕ)
    (f : Matching n d → (Fin n → m.Spin) → Finset (Fin n) → ℝ) :
    (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
      planted m t M σ * gibbs m t M σ' * revealProb s U * f M σ U) =
        plantedPinnedE m t s d n f := by sorry
