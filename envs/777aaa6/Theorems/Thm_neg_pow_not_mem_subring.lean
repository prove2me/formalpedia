-- Prove2me | Theorems.Thm_neg_pow_not_mem_subring
-- name    : neg_pow_not_mem_subring
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:46:56.01775+00:00
-- url     : https://prove2.me/theorems/3a42346d-6c6a-4096-a94d-71d2055b973e
-- title:
--   neg pow not mem subring: neg pow not mem subring
-- statement:
--   The neg pow not mem subring construction uses the neg pow not mem subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L230-L253
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L230-L253

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]
include hϖ
omit [ValuationRing R] [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K]

theorem neg_pow_not_mem_subring (n : ℕ) (hn : n > 0) : ϖ.val ^ (- n : ℤ) ∉ R := by sorry
