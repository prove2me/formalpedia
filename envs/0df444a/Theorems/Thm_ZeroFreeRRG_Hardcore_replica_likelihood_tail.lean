-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_replica_likelihood_tail
-- name    : ZeroFreeRRG.Hardcore.replica_likelihood_tail
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T10:09:56.913612+00:00
-- url     : https://prove2.me/theorems/1ea7b2aa-ead1-416b-8e5f-6fa7b2ada5a3
-- title:
--   Exponential two-replica likelihood-density tail
-- statement:
--   Under Condition 1 for either positive-parameter model, for every $\eta>0$ there are a reveal probability $s\in(0,1)$ and $c>0$ such that, for all sufficiently large admissible $n$, the planted joint probability that the two pinned log-likelihoods sum to more than $s\eta^2 n/24$ is at most $2e^{-cn}$. This is the density-tail estimate in Lemma 5.6, with $b=s\eta^2/12$.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.replica_likelihood_tail (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.PosParam t)
    (hC1 : Condition1 m d t) (η : ℝ) (hη : 0 < η) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
      ∀ n ≥ N, Even (n*d) →
      (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
        planted m t M σ * gibbs m t M σ' * revealProb s U *
          (if pinnedLL m t M σ U + pinnedLL m t M σ' U > (s*η^2/24)*n then 1 else 0)) ≤
        2*Real.exp (-c*n) := by sorry
