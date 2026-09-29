-- Prove2me | Theorems.Thm_MarkovEntanglement_separable_iff_resolvent_separable
-- name    : MarkovEntanglement.separable_iff_resolvent_separable
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-07T05:24:21.817264+00:00
-- url     : https://prove2.me/theorems/a6c0b6c6-e907-4bce-a55b-8085fa9d036d
-- title:
--   Separability is preserved by passing to the resolvent
-- statement:
--   ## Statement
--
--   **Lemma.** For any transition matrix $P$ and any $\gamma \in (0,1)$,
--   $$P \text{ is separable} \iff (1-\gamma)(I - \gamma P)^{-1} \text{ is separable}.$$
--
--   ## Notes
--
--   The discounted resolvent $(1-\gamma)(I-\gamma P)^{-1}$ is itself a transition matrix — it is
--   the normalised discounted occupancy kernel — and this lemma says separability transfers
--   between a chain and its resolvent in both directions.
--
--   The forward direction is a short computation from the Neumann series
--   $(1-\gamma)\sum_{k \ge 0} (\gamma P)^k$: each power of a separable matrix stays separable, and
--   so does an affine combination. The reverse direction is the harder one and goes through a
--   spectral-radius argument. The equivalence lets one move freely between the one-step picture,
--   where separability is defined, and the discounted picture, where value functions live.
--
--   Search terms: discounted occupancy kernel, Neumann series of a stochastic matrix, resolvent
--   of a Markov chain, separability under matrix inversion.
-- source:
--   Shuze Chen and Tianyi Peng, *Multi-agent Markov Entanglement*, arXiv:2506.02385v3, Lemma 4, p. 35

import Mathlib
import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

theorem separable_iff_resolvent_separable
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hP : IsTransitionMatrix P) :
    IsSeparableN P ↔ IsSeparableN ((1 - γ) • (1 - γ • P)⁻¹) := by
  sorry

end MarkovEntanglement
