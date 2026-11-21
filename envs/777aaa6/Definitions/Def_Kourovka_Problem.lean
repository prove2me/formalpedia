-- Prove2me | Definitions.Def_Kourovka_Problem
-- name    : Kourovka_Problem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:28:19.996875+00:00
-- url     : https://prove2.me/theorems/94c8b7e8-921d-4e24-8567-bf0f601cb19e
-- title:
--   Problem
-- statement:
--   Definitions and structural lemmas for Problem, from Achyuth Jayadevan's pinned Direct products of soluble Hopfian groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/Problem.lean

import Definitions.Def_Kourovka_Hopfian
set_option autoImplicit true
namespace Kourovka
def ProductHopficityStatement (A B : Type*) [Group A] [Group B] : Prop :=
  Group.FG A → Group.FG B → IsSolvable A → IsSolvable B →
    IsHopfian A → IsHopfian B → IsHopfian (A × B)
end Kourovka


