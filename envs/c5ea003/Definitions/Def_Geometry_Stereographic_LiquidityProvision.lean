-- Prove2me | Definitions.Def_Geometry_Stereographic_LiquidityProvision
-- name    : Geometry_Stereographic_LiquidityProvision
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:06.309175+00:00
-- url     : https://prove2.me/theorems/8e4bc585-f9a8-40fb-b370-8533ecfa5133
-- title:
--   Aether Catalog definitions — Geometry_Stereographic_LiquidityProvision
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Stereographic.LiquidityProvision`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Stereographic/LiquidityProvision.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Cryptography.Ethereum.LiquidityProvision

Auto-generated from theorem catalog database.
Domain: Cryptography/Ethereum
Declarations: 13
-/

noncomputable section

/-- **Impermanent Loss Factor**: Given initial price p₀ and current price p₁,
the impermanent loss factor for a constant-product AMM.
IL(r) = 2√r / (1 + r) - 1, where r = p₁/p₀
This measures the percentage loss compared to simply holding the tokens. -/
noncomputable def impermanentLossFactor (r : ℝ) (hr : 0 < r) : ℝ :=
  2 * Real.sqrt r / (1 + r) - 1




/-- Parameters for LP profitability analysis -/
structure LPPosition where
  initialValue : ℝ         -- Initial deposit value (in USD)
  priceRatio : ℝ           -- Final/initial price ratio
  feeAPR : ℝ               -- Annual fee income as fraction of position
  holdingPeriod : ℝ         -- In years
  hValue : 0 < initialValue
  hRatio : 0 < priceRatio
  hFee : 0 ≤ feeAPR
  hPeriod : 0 < holdingPeriod

/-- Value of hodling (not providing liquidity) -/
noncomputable def hodlValue (lp : LPPosition) : ℝ :=
  lp.initialValue * (1 + lp.priceRatio) / 2

/-- Value from LP position (pool value + fees earned) -/
noncomputable def lpValue (lp : LPPosition) : ℝ :=
  lp.initialValue * Real.sqrt lp.priceRatio +
  lp.initialValue * lp.feeAPR * lp.holdingPeriod


/-- A concentrated liquidity position with price range [pₐ, p_b] -/
structure ConcentratedPosition where
  pLower : ℝ    -- Lower price bound
  pUpper : ℝ    -- Upper price bound
  liquidity : ℝ  -- Liquidity parameter L
  hLower : 0 < pLower
  hUpper : 0 < pUpper
  hRange : pLower < pUpper
  hLiq : 0 < liquidity

/-- **Capital Efficiency Amplification**: Concentrated liquidity over range
[pₐ, p_b] provides the same depth as (p_b/pₐ)^(1/2) times more capital
in a full-range position. -/
noncomputable def capitalEfficiency (cp : ConcentratedPosition) : ℝ :=
  Real.sqrt (cp.pUpper / cp.pLower)




end


