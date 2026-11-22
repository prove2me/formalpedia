-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.boundedSearch_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:16:25.803866+00:00
-- url     : https://prove2.me/submissions/97f5fc16-4ce6-4d3c-9a6a-f34549312666

import Mathlib.Computability.Halting
import Mathlib.Tactic
import Definitions.Def_Kourovka_Computability_Enumeration
import Theorems.Thm_Kourovka_MetabelianEnumeration_boundedSearch_iff

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration
namespace Kourovka.MetabelianEnumeration
theorem _root_.solution (check : ℕ → ℕ → Bool) (P : ℕ → Prop)
    (sound : ∀ p c, check p c = true → P p) (p n : ℕ)
    (h : boundedSearch check p n = true) : P p := by
  obtain ⟨c, _, hc⟩ := (boundedSearch_iff check p n).mp h
  exact sound p c hc
end Kourovka.MetabelianEnumeration
