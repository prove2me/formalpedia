-- Prove2me | solution 1 for valuation_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:54:45.571034+00:00
-- url     : https://prove2.me/submissions/b3c60912-71c6-46b4-9018-cb96a0c67ffb

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Theorems.Thm_valuation_unit

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
theorem _root_.solution (a : R) (ha : IsUnit a) : v a = 1 :=
  valuation_unit ha.unit
