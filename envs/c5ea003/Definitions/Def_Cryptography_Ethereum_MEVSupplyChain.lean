-- Prove2me | Definitions.Def_Cryptography_Ethereum_MEVSupplyChain
-- name    : Cryptography_Ethereum_MEVSupplyChain
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:12:36.154547+00:00
-- url     : https://prove2.me/theorems/f94af96e-c970-4446-866f-d4a64b084a38
-- title:
--   Aether Catalog definitions — Cryptography_Ethereum_MEVSupplyChain
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.Ethereum.MEVSupplyChain`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/Ethereum/MEVSupplyChain.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Cryptography.Ethereum.MEVSupplyChain

Auto-generated from theorem catalog database.
Domain: Cryptography/Ethereum
Declarations: 13
-/

noncomputable section

/-- [Section: # CatalogBuild.Cryptography.Ethereum.MEVSupplyChain
Auto-generated from theorem catalog database.
Domain: Cryptography/Ethereum
Declarations: 13] -/
structure Builder where
  efficiency : ℝ
  cost : ℝ
  hEff0 : 0 < efficiency
  hEff1 : efficiency ≤ 1
  hCost : 0 ≤ cost

/-- [Section: # CatalogBuild.Cryptography.Ethereum.MEVSupplyChain
Auto-generated from theorem catalog database.
Domain: Cryptography/Ethereum
Declarations: 13] -/
noncomputable def builderProfit (b : Builder) (totalMEV bid : ℝ) : ℝ :=
  b.efficiency * totalMEV - b.cost - bid


structure SpecializedBuilder extends Builder where
  specialtyFraction : ℝ
  specialtyEfficiency : ℝ
  hSpecFrac0 : 0 ≤ specialtyFraction
  hSpecFrac1 : specialtyFraction ≤ 1
  hSpecEff : efficiency ≤ specialtyEfficiency
  hSpecEff1 : specialtyEfficiency ≤ 1

noncomputable def specializedCapture (sb : SpecializedBuilder) (totalMEV : ℝ) : ℝ :=
  sb.specialtyEfficiency * sb.specialtyFraction * totalMEV +
  sb.efficiency * (1 - sb.specialtyFraction) * totalMEV

noncomputable def generalCapture (sb : SpecializedBuilder) (totalMEV : ℝ) : ℝ :=
  sb.efficiency * totalMEV


noncomputable def mevShareUserReturn (totalMEV userShare : ℝ) : ℝ :=
  userShare * totalMEV




noncomputable def lateMevGain (baseMEV delayMs mevGrowthRate : ℝ) : ℝ :=
  baseMEV + delayMs * mevGrowthRate


end


