-- Prove2me | Theorems.Thm_Submodule_FG_source_of_le
-- name    : Submodule.FG.source_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:54:34.746088+00:00
-- url     : https://prove2.me/theorems/c49bb8e8-1166-48cf-af14-302754b0e9f0
-- title:
--   FG: source of le
-- statement:
--   The FG construction uses the source of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L119-L121
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L119-L121

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc
set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [IsNoetherianRing R]

theorem Submodule.FG.source_of_le {p q : Submodule R M} (hpq : p ≤ q) (hfg : q.FG) :
    p.FG := by sorry
