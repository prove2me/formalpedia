-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_4_20_pinned_concentration
-- name    : ZeroFreeRRG.Hardcore.lemma_4_20_pinned_concentration
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T10:46:41.952228+00:00
-- url     : https://prove2.me/theorems/e3944952-e9e1-4c4a-b568-f0f364a06747
-- title:
--   Lemma 4.20: concentration of the pinned log-likelihood
-- statement:
--   For every reveal rate s in [0,1] and b>0, the planted probability that the pinned log-likelihood exceeds its mean by bn is exponentially small in n along admissible indices.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 31, Lemma 4.20 and equation (29).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
open scoped Classical
open Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore

theorem ZeroFreeRRG.Hardcore.lemma_4_20_pinned_concentration (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.PosParam t) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ b : ℝ, 0 < b → ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, Even (n * d) →
        plantedPinnedE m t s d n (fun M σ U =>
            if pinnedLL m t M σ U - plantedPinnedE m t s d n (fun M' σ' U' => pinnedLL m t M' σ' U')
                > b * n then 1 else 0) ≤ Real.exp (-c * n) := by sorry
