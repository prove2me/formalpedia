-- Prove2me | solution 1 for irreducible_zpow_mem_subring_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:59:13.807349+00:00
-- url     : https://prove2.me/submissions/3163a8f5-aca6-4925-b8bd-3b646f3a6434

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Theorems.Thm_neg_pow_not_mem_subring

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]
omit [ValuationRing R] [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K]
include hϖ
theorem _root_.solution (n : ℤ) : ϖ.val ^ n ∈ R ↔ n ≥ 0 := by
  constructor
  · intro h
    contrapose! h
    have hn : - n ≥ 0 := by omega
    convert_to (ϖ.val ^ (- (- n).toNat : ℤ)) ∉ R
    · rw [Int.toNat_of_nonneg hn]
      simp
    · apply neg_pow_not_mem_subring _ (-n).toNat (hϖ := hϖ)
      simpa
  · intro hn
    convert_to (ϖ ^ n.toNat).val ∈ R
    · rw [SubmonoidClass.coe_pow, ← zpow_natCast, Int.toNat_of_nonneg hn]
    · exact SetLike.coe_mem (ϖ ^ n.toNat)
