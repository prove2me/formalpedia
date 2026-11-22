-- Prove2me | solution 1 for zaddVal_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:57:05.043178+00:00
-- url     : https://prove2.me/submissions/2cdece8a-6e3b-4f9b-ae24-3553c9ed293a

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Theorems.Thm_P2M_zaddVal__spec_8ebf7135ac48
import Theorems.Thm_P2M_zaddVal_spec__8e01bd6b150a

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]
theorem _root_.solution (x : Kˣ) : ∃ (ϖ : R) (hϖ : Irreducible ϖ)
    (u : Rˣ),
    x = Units.map R.subtype u *
      (Units.mk0 ϖ.val (by simpa using hϖ.ne_zero)) ^ (zaddVal (R := R) x) := by
  obtain ⟨ϖ, hϖ, h⟩ := zaddVal_spec' (R := R) x
  use ϖ, hϖ
  obtain ⟨u, hu⟩ := zaddVal'_spec ϖ hϖ x
  use u
  rwa [h]
