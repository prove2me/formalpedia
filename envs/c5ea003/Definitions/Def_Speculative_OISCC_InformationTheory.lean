-- Prove2me | Definitions.Def_Speculative_OISCC_InformationTheory
-- name    : Speculative_OISCC_InformationTheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:34:34.916206+00:00
-- url     : https://prove2.me/theorems/9254e5c3-4b58-4c85-9c73-d351f8a18509
-- title:
--   Aether Catalog definitions — Speculative_OISCC_InformationTheory
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.OISCC.InformationTheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/OISCC/InformationTheory.lean by skeleton subtraction
import Mathlib
/-
# OISCC V10: EML as an Information-Theoretic Primitive

Channel sensitivity, SNR, amplification, Fisher information.
-/


noncomputable section

open Real Filter Topology Set

def EML_info (a b : ℝ) : ℝ := Real.exp a - Real.log b

/-! ## Channel Sensitivity -/



/-! ## Signal-to-Noise Ratio -/

def EML_SNR (a b : ℝ) : ℝ := Real.exp a * b




/-! ## Amplification -/




/-! ## Mutual Information Analog -/

def EML_MI (x y : ℝ) : ℝ :=
  EML_info x y + EML_info y x - EML_info x x - EML_info y y


/-! ## Fisher Information -/

def fisher_info_a (a : ℝ) : ℝ := (Real.exp a) ^ 2



end


