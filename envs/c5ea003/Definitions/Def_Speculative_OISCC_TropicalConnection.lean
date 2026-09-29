-- Prove2me | Definitions.Def_Speculative_OISCC_TropicalConnection
-- name    : Speculative_OISCC_TropicalConnection
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:34:35.819558+00:00
-- url     : https://prove2.me/theorems/f3238954-1d79-4b1e-a006-bb7d345be196
-- title:
--   Aether Catalog definitions — Speculative_OISCC_TropicalConnection
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.OISCC.TropicalConnection`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/OISCC/TropicalConnection.lean by skeleton subtraction
import Mathlib
/-
# OISCC V10: EML and Tropical Mathematics

EML(a,b) = exp(a) - ln(b) lifts tropical subtraction to the exponential world.
-/


noncomputable section

open Real Filter Topology Set

def EML_trop (a b : ℝ) : ℝ := Real.exp a - Real.log b


def tropVal (x : ℝ) : ℝ := Real.log x


def logSumExp (a b : ℝ) : ℝ := Real.log (Real.exp a + Real.exp b)





def EML_poly1 (a b c x : ℝ) : ℝ := EML_trop (a + b * x) c


/-
EML grows super-polynomially.
-/

end


