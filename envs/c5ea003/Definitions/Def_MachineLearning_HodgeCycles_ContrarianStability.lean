-- Prove2me | Definitions.Def_MachineLearning_HodgeCycles_ContrarianStability
-- name    : MachineLearning_HodgeCycles_ContrarianStability
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:43:50.05969+00:00
-- url     : https://prove2.me/theorems/99ea66a9-7585-4618-a152-17a6f399f571
-- title:
--   Aether Catalog definitions — MachineLearning_HodgeCycles_ContrarianStability
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.HodgeCycles.ContrarianStability`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/HodgeCycles/ContrarianStability.lean by skeleton subtraction
import Mathlib

namespace MachineLearning.HodgeCycles.ContrarianStability

/-- All three chain groups in the counterexample are one-dimensional over `ℚ`. -/
abbrev ChainSpace := ℚ

/-- Multiplication by `t`, viewed as the lower cellular differential. -/
def lowerBoundary (t : ℚ) : ChainSpace →ₗ[ℚ] ChainSpace :=
  (LinearMap.lsmul ℚ ChainSpace) t

/-- The upper differential in the family is zero. -/
def upperBoundary : ChainSpace →ₗ[ℚ] ChainSpace := 0

/-- A middle-chain element is a cycle when the lower differential kills it. -/
def IsMiddleCycle (t x : ℚ) : Prop := lowerBoundary t x = 0

/-- A middle-chain element is a boundary when it lies in the image of the upper
boundary map. -/
def IsMiddleBoundary (x : ℚ) : Prop :=
  ∃ y : ℚ, upperBoundary y = x

/-- Constructive nonvanishing of middle homology: some cycle is not a boundary. -/
def HasNonzeroMiddleHomology (t : ℚ) : Prop :=
  ∃ x : ℚ, IsMiddleCycle t x ∧ ¬ IsMiddleBoundary x










end MachineLearning.HodgeCycles.ContrarianStability


