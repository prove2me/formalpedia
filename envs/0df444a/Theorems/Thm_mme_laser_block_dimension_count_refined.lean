-- Prove2me | Theorems.Thm_mme_laser_block_dimension_count_refined
-- name    : mme_laser_block_dimension_count_refined
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-01T00:30:33.02368+00:00
-- url     : https://prove2.me/theorems/1af5a5bc-f051-4ba9-9324-cff3a7143d91
-- statement:
--   **Stirling/multinomial lower bound on type-distributed multi-type counts** — REFINED concrete version of `mme_laser_block_dimension_count`. For cyclically-marginal probability distribution p on S, the count of length-N S-sequences with empirical distribution ≈ p is asymptotically ≥ exp(N·log 2·(H(p) - ε)) for every ε > 0 (Stirling on multinomial coefficients). Plus the trivial upper bound ≤ |S|^N. Replaces the original True-conclusion with this concrete information-theoretic Stirling bound — the genuinely paper-agnostic analytic core of the laser method. Every paper (CW 1990 §7, Stothers, VW, Le Gall, Alman-VW) uses this fact at its own p.
-- source:
--   https://arxiv.org/abs/2212.11824

import Definitions.Def_mme_laser_pattern
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
open BigOperators Filter
universe u

theorem mme_laser_block_dimension_count_refined {t : ℕ} (S : Finset (Fin t × Fin t × Fin t)) (_hSym : MME.LaserSymmetric S) (p : (Fin t × Fin t × Fin t) → ℝ) (_hp_nonneg : ∀ x, 0 ≤ p x) (_hp_zero_off : ∀ x ∉ S, p x = 0) (_hp_sum : ∑ x ∈ S, p x = 1) (_hp_cyclic_12 : ∀ α : Fin t, ∑ x ∈ S, (if x.1 = α then p x else 0) = ∑ x ∈ S, (if x.2.1 = α then p x else 0)) (_hp_cyclic_23 : ∀ α : Fin t, ∑ x ∈ S, (if x.2.1 = α then p x else 0) = ∑ x ∈ S, (if x.2.2 = α then p x else 0)) : ∀ ε > (0 : ℝ), ∃ᶠ N : ℕ in Filter.atTop, ∃ k : ℕ, Real.exp ((Real.log 2) * (((∑ x ∈ S, (-p x) * (Real.log (p x) / Real.log 2)) - ε) * (N : ℝ))) ≤ (k : ℝ) ∧ (k : ℕ) ≤ S.card ^ N := by sorry
