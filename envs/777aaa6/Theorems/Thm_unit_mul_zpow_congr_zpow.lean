-- Prove2me | Theorems.Thm_unit_mul_zpow_congr_zpow
-- name    : unit_mul_zpow_congr_zpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:45:29.934242+00:00
-- url     : https://prove2.me/theorems/b159d73a-913c-41b3-a3f7-099b768f249e
-- title:
--   unit mul zpow congr zpow: unit mul zpow congr zpow
-- statement:
--   The unit mul zpow congr zpow construction uses the unit mul zpow congr zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L188-L198
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L188-L198

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]

theorem unit_mul_zpow_congr_zpow {p q : R} (hp : Irreducible p) (hq : Irreducible q)
    (a b : Rˣ) (m n : ℤ) (h : a * p.val ^ m = b * q.val ^ n) :
    m = n := by sorry
