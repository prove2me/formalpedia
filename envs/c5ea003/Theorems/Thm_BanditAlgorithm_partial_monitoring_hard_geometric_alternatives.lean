-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_hard_geometric_alternatives
-- name    : BanditAlgorithm.partial_monitoring_hard_geometric_alternatives
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T17:45:19.255122+00:00
-- url     : https://prove2.me/theorems/22a0c0a1-e702-41f4-bda9-47d22fcb0aff
-- title:
--   Geometric alternatives for a hard partial-monitoring edge
-- statement:
--   Let $G$ be globally observable but not locally observable. There exist neighbouring actions $a,b$, a base distribution $u$, a zero-sum normalized direction $q$, and constants $\varepsilon,\delta>0$ such that the alternatives $u\pm\Delta q$ have the cell, loss-gap, feedback-indistinguishability, and Eq. (37.10) properties for every $0<\Delta\le\delta$.
--
--   $$
--   \langle\ell_c-\ell_a,u-\Delta q\rangle+\langle\ell_c-\ell_b,u+\Delta q\rangle=\Delta.
--   $$
--
--   This packages the geometric half of the hard partial-monitoring lower bound.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge UP, 2020), Theorem 37.12, Steps 1 and 3, printed pp. 488–491, Eqs. (37.5)–(37.7) and (37.10); Lemma 37.8(a), printed pp. 484–485.

import Definitions.Def_PartialMonitoringGame

theorem BanditAlgorithm.partial_monitoring_hard_geometric_alternatives
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [DecidableEq 𝕊]
    (G : BanditAlgorithm.PartialMonitoringGame k d 𝕊)
    (hglob : BanditAlgorithm.GloballyObservable G)
    (hloc : ¬ BanditAlgorithm.LocallyObservable G) :
    ∃ a b : Fin k, ∃ u q : Fin d → ℝ, ∃ ε δ : ℝ,
      BanditAlgorithm.NeighbouringActions G a b ∧ 0 < ε ∧ 0 < δ ∧
      (∑ i, q i) = 0 ∧
      (∑ i, (G.L a i - G.L b i) * q i) = 1 ∧
      (∀ c : Fin k, c ∈ BanditAlgorithm.pmNeighbourhood G a b → ∀ σ : 𝕊,
        ∑ i ∈ Finset.univ.filter (fun i ↦ G.Φ c i = σ), q i = 0) ∧
      ∀ Δ : ℝ, 0 < Δ → Δ ≤ δ →
        let ua := fun i ↦ u i - Δ * q i
        let ub := fun i ↦ u i + Δ * q i
        ua ∈ BanditAlgorithm.pmCell G a ∧ ub ∈ BanditAlgorithm.pmCell G b ∧
        (∀ c : Fin k, c ∉ BanditAlgorithm.pmNeighbourhood G a b →
          ε / 2 ≤ ∑ i, (G.L c i - G.L a i) * ua i ∧
          ε / 2 ≤ ∑ i, (G.L c i - G.L b i) * ub i) ∧
        (∀ c : Fin k, c ∈ BanditAlgorithm.pmNeighbourhood G a b →
          (∑ i, (G.L c i - G.L a i) * ua i) +
          (∑ i, (G.L c i - G.L b i) * ub i) = Δ) :=
  by sorry
