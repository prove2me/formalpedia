-- Prove2me | solution 1 for valuation_unit_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:54:47.698858+00:00
-- url     : https://prove2.me/submissions/28809ee4-3e20-4255-acd6-8a7d4047b02f

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Theorems.Thm_valuation_unit

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
theorem _root_.solution (x : Rˣ) : v x = 1 :=
  valuation_unit x
