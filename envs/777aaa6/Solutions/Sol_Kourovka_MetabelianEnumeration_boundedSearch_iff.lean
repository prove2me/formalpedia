-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.boundedSearch_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:40:32.630049+00:00
-- url     : https://prove2.me/submissions/9528fd4d-25ad-4a36-bcef-11f9a4d590f9

import Mathlib.Computability.Halting
import Mathlib.Tactic
import Definitions.Def_Kourovka_Computability_Enumeration

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration
namespace Kourovka.MetabelianEnumeration
theorem _root_.solution (check : ℕ → ℕ → Bool) (p n : ℕ) :
    boundedSearch check p n = true ↔ ∃ c < n, check p c = true := by
  simp [boundedSearch, List.any_eq_true, List.mem_range]
end Kourovka.MetabelianEnumeration
