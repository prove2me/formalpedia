-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_planted_reveal_change_measure
-- name    : ZeroFreeRRG.Hardcore.planted_reveal_change_measure
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:23:14.382549+00:00
-- url     : https://prove2.me/theorems/476a9e3e-937b-4cb5-bf61-826618d98113
-- title:
--   Planted two-replica revealed-event change of measure
-- statement:
--   For the planted graph with two Gibbs replicas and a Bernoulli reveal set, assume the product-prior probability of a revealed-pattern event is at most $R$. The planted joint probability of that event together with the condition that the two pinned log-likelihoods sum to at most $B$ is at most $e^B R$. The formula retains all finite matching, spin, and reveal-set sums.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, pp. 39–40, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.planted_reveal_change_measure (m : Model) (hm : m.Valid) (t s : ℝ) (ht : m.PosParam t)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (d n : ℕ) [Nonempty (Matching n d)] (a₀ : m.Spin) (B R : ℝ)
    (H : ∀ U : Finset (Fin n), ({v : Fin n // v ∈ U} → m.Spin) →
      ({v : Fin n // v ∈ U} → m.Spin) → Prop)
    (hreference : (∑ U : Finset (Fin n), revealProb s U *
      ∑ y : ({v : Fin n // v ∈ U} → m.Spin), ∑ y' : ({v : Fin n // v ∈ U} → m.Spin),
        if H U y y' then
          (∏ v : {v : Fin n // v ∈ U}, m.pi t (y v)) *
          (∏ v : {v : Fin n // v ∈ U}, m.pi t (y' v)) else 0) ≤ R) :
    (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
      planted m t M σ * gibbs m t M σ' * revealProb s U *
        (if H U (fun v => σ v.1) (fun v => σ' v.1) ∧
            pinnedLL m t M σ U + pinnedLL m t M σ' U ≤ B then 1 else 0)) ≤ Real.exp B * R := by sorry
