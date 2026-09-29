-- Prove2me | Definitions.Def_Speculative_Computation_InformationTheory
-- name    : Speculative_Computation_InformationTheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:32:05.881109+00:00
-- url     : https://prove2.me/theorems/65634c13-ef40-41b8-8393-d17f5bd3a57c
-- title:
--   Aether Catalog definitions — Speculative_Computation_InformationTheory
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.Computation.InformationTheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/Computation/InformationTheory.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Computation.InformationTheory

Auto-generated from theorem catalog database.
Domain: Computation
Declarations: 15
-/


noncomputable section

/-- [Section: # CatalogBuild.Computation.InformationTheory
Auto-generated from theorem catalog database.
Domain: Computation
Declarations: 15] -/
def EML_info (a b : ℝ) : ℝ := Real.exp a - Real.log b












/-- [Section: # CatalogBuild.Computation.InformationTheory
Auto-generated from theorem catalog database.
Domain: Computation
Declarations: 15] -/
def EML_SNR (a b : ℝ) : ℝ := Real.exp a * b




























def EML_MI (x y : ℝ) : ℝ :=
  EML_info x y + EML_info y x - EML_info x x - EML_info y y








def fisher_info_a (a : ℝ) : ℝ := (Real.exp a) ^ 2












end


