-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_planted_replica_reveal_weight_nonnegative
-- name    : ZeroFreeRRG.Hardcore.planted_replica_reveal_weight_nonnegative
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:07:03.529333+00:00
-- url     : https://prove2.me/theorems/278967e9-e21e-4540-903f-7340ccd4d1e7
-- title:
--   Nonnegativity of planted replica and reveal weights
-- statement:
--   For a valid positive-parameter model and a reveal probability in the unit interval, the joint weights of a planted configuration, an independent Gibbs replica, and a reveal set are nonnegative.
-- source:
--   Auxiliary identity for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.planted_replica_reveal_weight_nonnegative (m : Model) (hm : m.Valid) (t s : ℝ) (ht : m.PosParam t)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (d n : ℕ) :
    ∀ (M : Matching n d) (σ σ' : Fin n → m.Spin) (U : Finset (Fin n)),
      0 ≤ planted m t M σ * gibbs m t M σ' * revealProb s U := by sorry
