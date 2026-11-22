-- Prove2me | solution 1 for P2M_zaddVal_spec__8e01bd6b150a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:54:52.35139+00:00
-- url     : https://prove2.me/submissions/989dab86-2fda-4685-9c3f-8dc4dee01e20

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]
theorem _root_.solution (x : Kˣ) : ∃ (ϖ : R) (hϖ : Irreducible ϖ),
    zaddVal (R := R) x = zaddVal' ϖ hϖ x := by
  use (IsDiscreteValuationRing.exists_irreducible R).choose
  use (IsDiscreteValuationRing.exists_irreducible R).choose_spec
  rfl
