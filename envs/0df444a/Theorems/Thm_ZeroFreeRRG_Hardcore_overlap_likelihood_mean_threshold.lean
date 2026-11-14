-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_overlap_likelihood_mean_threshold
-- name    : ZeroFreeRRG.Hardcore.overlap_likelihood_mean_threshold
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T10:01:13.932181+00:00
-- url     : https://prove2.me/theorems/e964d9c6-355f-4305-bbc6-c1ff10342fa4
-- title:
--   The planted log-likelihood mean lies below the reveal threshold
-- statement:
--   Under Condition 1 for either positive-parameter model, for every $\eta>0$ one can choose a reveal probability $s\in(0,1)$ so that, for all sufficiently large admissible $n$, the planted expectation of the pinned log-likelihood is at most $s\eta^2 n/96$. This is precisely the $bn/8$ mean bound with $b=s\eta^2/12$ used in the proof of the exponential overlap bound.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.overlap_likelihood_mean_threshold (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.PosParam t)
    (hC1 : Condition1 m d t) (η : ℝ) (hη : 0 < η) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∃ N : ℕ,
      ∀ n ≥ N, Even (n*d) →
        plantedPinnedE m t s d n (fun M σ U => pinnedLL m t M σ U) ≤ (s*η^2/96)*n := by sorry
