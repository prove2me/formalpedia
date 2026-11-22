-- Prove2me | solution 1 for P2M_zaddVal__spec_8ebf7135ac48
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:45:52.615205+00:00
-- url     : https://prove2.me/submissions/7e7dfb82-0de7-4630-8ec8-cf9d8e445bd1

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]
theorem _root_.solution (x : Kˣ) : ∃ (u : Rˣ),
    x = Units.map R.subtype u *
      (Units.mk0 ϖ.val (by simpa using hϖ.ne_zero)) ^ (zaddVal' ϖ hϖ x) :=
  (eq_unit_mul_pow_irreducible' ϖ hϖ x).choose_spec
