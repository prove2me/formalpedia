-- Prove2me | solution 1 for valuation_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:45:45.439038+00:00
-- url     : https://prove2.me/submissions/6e796e3a-185e-4714-9bf3-27574937a632

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
theorem _root_.solution (x y : K) :
    v x = v y ↔ ∃ (a : Rˣ), a * y = x :=
  Quotient.eq''
