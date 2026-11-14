-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_overlap_pinned_likelihood_tail
-- name    : ZeroFreeRRG.Hardcore.overlap_pinned_likelihood_tail
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T10:02:02.508552+00:00
-- url     : https://prove2.me/theorems/bb4dc758-66de-41eb-a0a4-236c833edd50
-- title:
--   Exponential tail for the pinned reveal log-likelihood
-- statement:
--   Under Condition 1 for either positive-parameter model, for every $\eta>0$ there exist $s\in(0,1)$ and $c>0$ such that for all sufficiently large admissible $n$, the planted probability that the pinned log-likelihood exceeds $s\eta^2 n/48$ is at most $e^{-cn}$. This is the likelihood-tail estimate in the proof of the exponential overlap bound.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.overlap_pinned_likelihood_tail (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.PosParam t)
    (hC1 : Condition1 m d t) (η : ℝ) (hη : 0 < η) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
      ∀ n ≥ N, Even (n*d) →
        plantedPinnedE m t s d n (fun M σ U =>
          if pinnedLL m t M σ U > (s*η^2/48)*n then 1 else 0) ≤ Real.exp (-c*n) := by sorry
