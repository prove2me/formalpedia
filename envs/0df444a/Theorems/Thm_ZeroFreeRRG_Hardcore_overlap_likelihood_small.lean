-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_overlap_likelihood_small
-- name    : ZeroFreeRRG.Hardcore.overlap_likelihood_small
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T09:55:12.433753+00:00
-- url     : https://prove2.me/theorems/7bba6e7e-bdb1-4a58-85d7-d30470920b25
-- title:
--   Small planted reveal log-likelihood under Condition 1
-- statement:
--   Under Condition 1 for either positive-parameter hardcore or Potts model, for every $\varepsilon>0$ there is a reveal probability $s\in(0,1)$ such that the planted expected pinned log-likelihood divided by $n$ is at most $\varepsilon s$ for all sufficiently large admissible $n$. This is the small-mean estimate used at the start of the proof of the exponential overlap bound.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6, from equation (29).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.overlap_likelihood_small (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.PosParam t)
    (hC1 : Condition1 m d t) :
    ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∃ N : ℕ,
      ∀ n ≥ N, Even (n*d) →
        (1:ℝ)/n * plantedPinnedE m t s d n (fun M σ U => pinnedLL m t M σ U) ≤ ε*s := by sorry
