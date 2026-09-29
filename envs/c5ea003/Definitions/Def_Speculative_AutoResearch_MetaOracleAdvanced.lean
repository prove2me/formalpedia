-- Prove2me | Definitions.Def_Speculative_AutoResearch_MetaOracleAdvanced
-- name    : Speculative_AutoResearch_MetaOracleAdvanced
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:29:00.951973+00:00
-- url     : https://prove2.me/theorems/3bfa00b5-0b27-4ba4-ab8d-f2bd906437e1
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_MetaOracleAdvanced
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.MetaOracleAdvanced`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/MetaOracleAdvanced.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Computation.Oracles.MetaOracleAdvanced

Auto-generated from theorem catalog database.
Domain: Computation/Oracles
Declarations: 12
-/


noncomputable section

/-- The identity meta-oracle: does nothing. -/
def metaOracleId {α : Type*} : α → α := id












/-- The improvement ratio after n steps of a contraction with rate k. -/
def improvementRatio (k : ℝ) (n : ℕ) : ℝ := 1 - k ^ n








/-- Number of iterations needed to achieve ε-optimality. -/
def iterationsNeeded (k ε d₀ : ℝ) : ℝ :=
  Real.log (ε / d₀) / Real.log k








/-- Meta-oracles on a fixed type form a semigroup under composition. -/
instance metaOracleSemigroup (α : Type*) : Semigroup (α → α) where
  mul := Function.comp
  mul_assoc := Function.comp_assoc




/-- Meta-oracles on a fixed type form a monoid with identity. -/
instance metaOracleMonoid (α : Type*) : Monoid (α → α) where
  one := id
  one_mul := Function.id_comp
  mul_one := Function.comp_id








/-- A weighted combination of quality values (portfolio quality). -/
def portfolioQuality {n : ℕ} (weights : Fin n → ℝ) (qualities : Fin n → ℝ) : ℝ :=
  ∑ i, weights i * qualities i








end


