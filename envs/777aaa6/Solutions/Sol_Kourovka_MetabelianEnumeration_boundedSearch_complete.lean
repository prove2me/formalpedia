-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.boundedSearch_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:16:42.320171+00:00
-- url     : https://prove2.me/submissions/95624e6b-0a23-41de-ad09-0aaa58af122f

import Mathlib.Computability.Halting
import Mathlib.Tactic
import Definitions.Def_Kourovka_Computability_Enumeration
import Theorems.Thm_Kourovka_MetabelianEnumeration_boundedSearch_iff

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration
namespace Kourovka.MetabelianEnumeration
theorem _root_.solution (check : ℕ → ℕ → Bool) (P : ℕ → Prop)
    (complete : ∀ p, P p → ∃ c, check p c = true) (p : ℕ) (hp : P p) :
    ∃ n, boundedSearch check p n = true := by
  obtain ⟨c, hc⟩ := complete p hp
  exact ⟨c + 1, (boundedSearch_iff check p (c + 1)).mpr ⟨c, by omega, hc⟩⟩
end Kourovka.MetabelianEnumeration
