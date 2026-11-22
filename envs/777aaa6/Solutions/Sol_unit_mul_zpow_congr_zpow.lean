-- Prove2me | solution 1 for unit_mul_zpow_congr_zpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:56:58.008206+00:00
-- url     : https://prove2.me/submissions/228618ba-1c26-477d-b6da-ca43a6944b87

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Theorems.Thm_P2M_unit_mul_zpow_congr_zpow__8af5a51cd3a7

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]
theorem _root_.solution {p q : R} (hp : Irreducible p) (hq : Irreducible q)
    (a b : Rˣ) (m n : ℤ) (h : a * p.val ^ m = b * q.val ^ n) :
    m = n := by
  obtain ⟨u, rfl⟩ := IsDiscreteValuationRing.associated_of_irreducible R hp hq
  simp at h
  rw [mul_zpow] at h
  nth_rw 3 [mul_comm] at h
  have : (b * u ^ n).val.val = b.val.val * u.val.val ^ n := by simp
  rw [← mul_assoc, ← this] at h
  apply unit_mul_zpow_congr_zpow' _ hp
  exact h
