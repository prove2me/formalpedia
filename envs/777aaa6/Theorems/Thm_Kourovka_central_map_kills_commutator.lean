-- Prove2me | Theorems.Thm_Kourovka_central_map_kills_commutator
-- name    : Kourovka.central_map_kills_commutator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:28:54.49984+00:00
-- url     : https://prove2.me/theorems/9bd67b5f-e267-472b-8b9d-df8f45dea330
-- title:
--   Kourovka: central map kills commutator
-- statement:
--   A homomorphism with central image vanishes on the derived subgroup.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/Components.lean#L58-L63
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/Components.lean#L58-L63

import Definitions.Def_Kourovka_Hopfian
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Prod
import Definitions.Def_Kourovka_Components
set_option autoImplicit true
open Kourovka
variable {A B K : Type*} [Group A] [Group B] [Group K]

theorem Kourovka.central_map_kills_commutator (f : A →* B)
    (hf : ∀ a, f a ∈ Subgroup.center B) : commutator A ≤ f.ker := by sorry
