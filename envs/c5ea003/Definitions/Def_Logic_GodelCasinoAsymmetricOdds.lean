-- Prove2me | Definitions.Def_Logic_GodelCasinoAsymmetricOdds
-- name    : Logic_GodelCasinoAsymmetricOdds
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:54:22.86143+00:00
-- url     : https://prove2.me/theorems/fb5c5493-3084-4bf5-bccf-6f4ec22bac1f
-- title:
--   Aether Catalog definitions — Logic_GodelCasinoAsymmetricOdds
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.GodelCasinoAsymmetricOdds`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/GodelCasinoAsymmetricOdds.lean by skeleton subtraction
import Mathlib
/-
# Gödel's Casino: asymmetric odds, transaction costs, and abstention

This file advances the randomized casino model from symmetric ±1 payoffs to
asymmetric odds.  A correct bet earns `a`, while an incorrect bet loses `b`.
The resulting break-even probability is `b / (a+b)` for betting true and
`a / (a+b)` for betting false.  We also add a zero-payoff abstention option.
-/

namespace GodelCasinoAsymmetricOdds

open Finset

variable {W : Type*} [Fintype W]

/-- Payoff of a pure Boolean bet: gain `a` when correct and lose `b` otherwise. -/
def oddsPayoff (s : W → Bool) (a b : ℚ) (bet : Bool) (ω : W) : ℚ :=
  if bet = s ω then a else -b

/-- Expected per-world payoff when `true` is bet with probability `r`. -/
def randOddsPayoff (s : W → Bool) (a b r : ℚ) (ω : W) : ℚ :=
  r * oddsPayoff s a b true ω + (1 - r) * oddsPayoff s a b false ω


/-- Prior mass of worlds where the statement is true. -/
def trueMass (μ : W → ℚ) (s : W → Bool) : ℚ :=
  ∑ ω, if s ω then μ ω else 0

/-- Prior mass of worlds where the statement is false. -/
def falseMass (μ : W → ℚ) (s : W → Bool) : ℚ :=
  ∑ ω, if s ω then 0 else μ ω


/-- Expected asymmetric-odds profit under a finite rational prior. -/
def expOdds (μ : W → ℚ) (s : W → Bool) (a b r : ℚ) : ℚ :=
  ∑ ω, μ ω * randOddsPayoff s a b r ω










/-- Optimal value when passing for zero payoff is allowed. -/
def abstentionValue (μ : W → ℚ) (s : W → Bool) (a b : ℚ) : ℚ :=
  max 0 (max (expOdds μ s a b 0) (expOdds μ s a b 1))




end GodelCasinoAsymmetricOdds


