-- Prove2me | Theorems.Thm_GodelCasinoAsymmetricOdds_edge_iff_outside_no_bet_interval
-- name    : GodelCasinoAsymmetricOdds.edge_iff_outside_no_bet_interval
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:25:22.26143+00:00
-- url     : https://prove2.me/theorems/3463f118-8a94-4a4f-87c5-8b41d7abe5ed
-- title:
--   Sharp profitability thresholds for asymmetric odds.
-- statement:
--   Sharp profitability thresholds for asymmetric odds.
--
--   ```lean
--   theorem GodelCasinoAsymmetricOdds.edge_iff_outside_no_bet_interval(μ : W → ℚ) (s : W → Bool) (a b : ℚ)
--       (hμ : ∑ ω, μ ω = 1) (hab : 0 < a + b) :
--       (∃ r, 0 ≤ r ∧ r ≤ 1 ∧ 0 < expOdds μ s a b r) ↔
--         trueMass μ s < a / (a + b) ∨ b / (a + b) < trueMass μ s := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/GodelCasinoAsymmetricOdds.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/GodelCasinoAsymmetricOdds.lean#L138

-- Thm stub generated from Logic/GodelCasinoAsymmetricOdds.lean
import Mathlib
import Definitions.Def_Logic_GodelCasinoAsymmetricOdds
/-
# Gödel's Casino: asymmetric odds, transaction costs, and abstention

This file advances the randomized casino model from symmetric ±1 payoffs to
asymmetric odds.  A correct bet earns `a`, while an incorrect bet loses `b`.
The resulting break-even probability is `b / (a+b)` for betting true and
`a / (a+b)` for betting false.  We also add a zero-payoff abstention option.
-/

open GodelCasinoAsymmetricOdds

open Finset

variable {W : Type*} [Fintype W]

theorem GodelCasinoAsymmetricOdds.edge_iff_outside_no_bet_interval(μ : W → ℚ) (s : W → Bool) (a b : ℚ)
    (hμ : ∑ ω, μ ω = 1) (hab : 0 < a + b) :
    (∃ r, 0 ≤ r ∧ r ≤ 1 ∧ 0 < expOdds μ s a b r) ↔
      trueMass μ s < a / (a + b) ∨ b / (a + b) < trueMass μ s := by sorry
