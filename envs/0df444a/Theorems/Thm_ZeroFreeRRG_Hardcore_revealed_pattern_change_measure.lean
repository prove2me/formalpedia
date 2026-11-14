-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_revealed_pattern_change_measure
-- name    : ZeroFreeRRG.Hardcore.revealed_pattern_change_measure
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:16:48.208835+00:00
-- url     : https://prove2.me/theorems/28448783-663a-4b01-871d-21f5c05d5e7f
-- title:
--   Change of measure for two revealed Gibbs replicas
-- statement:
--   Fix a configuration multigraph, reveal set, and event depending only on the two revealed spin patterns. If spin prior probabilities are positive and Gibbs weights are nonnegative, then the joint Gibbs weight of the revealed event restricted to a sum of pinned log-likelihoods at most $B$ is at most $e^B$ times the independent product-prior probability of the revealed event. This holds also for zero-weight patterns.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, pp. 39–40, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.revealed_pattern_change_measure (m : Model) (t : ℝ) (d n : ℕ) (M : Matching n d)
    (U : Finset (Fin n)) (a₀ : m.Spin) (B : ℝ)
    (H : ({v : Fin n // v ∈ U} → m.Spin) → ({v : Fin n // v ∈ U} → m.Spin) → Prop)
    (hπ : ∀ a, 0 < m.pi t a) (hnonneg : ∀ σ, 0 ≤ gibbs m t M σ) :
    let obs := fun (σ : Fin n → m.Spin) (v : {v : Fin n // v ∈ U}) => σ v.1
    let extend := fun (y : {v : Fin n // v ∈ U} → m.Spin) (v : Fin n) =>
      if h : v ∈ U then y ⟨v,h⟩ else a₀
    let prior := fun y => ∏ v ∈ U, m.pi t (extend y v)
    (∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin,
      if H (obs σ) (obs σ') ∧ pinnedLL m t M σ U + pinnedLL m t M σ' U ≤ B then
        gibbs m t M σ * gibbs m t M σ' else 0) ≤
      Real.exp B * ∑ y, ∑ y', if H y y' then prior y * prior y' else 0 := by sorry
