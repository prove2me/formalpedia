-- Prove2me | solution 1 for Submodule.FG.source_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:01:16.362095+00:00
-- url     : https://prove2.me/submissions/4a80138a-4307-477c-bfa7-9a027b2d95fc

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc

set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [IsNoetherianRing R]
namespace Submodule.FG
theorem _root_.solution {p q : Submodule R M} (hpq : p ≤ q) (hfg : q.FG) :
    p.FG :=
  isNoetherian_submodule.mp (isNoetherian_of_fg_of_noetherian q hfg) p hpq
end Submodule.FG
