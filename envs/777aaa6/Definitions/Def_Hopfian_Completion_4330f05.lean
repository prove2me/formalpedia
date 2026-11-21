-- Prove2me | Definitions.Def_Hopfian_Completion_4330f05
-- name    : Hopfian_Completion_4330f05
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:50:00.461684+00:00
-- url     : https://prove2.me/theorems/b567b052-7cba-4f31-8193-a67188c91861
-- title:
--   Completion
-- statement:
--   Definitions and structural lemmas for Completion, from Achyuth Jayadevan's pinned Direct products of soluble Hopfian groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Completion.lean

import Definitions.Def_Kourovka_Paper
import Theorems.Thm_Kourovka_problem_5_38

set_option autoImplicit true
example (A B : Type*) [Group A] [Group B]
    (hfgA : Group.FG A) (hfgB : Group.FG B)
    (hsolA : IsSolvable A) (hsolB : IsSolvable B)
    (hhopA : Kourovka.IsHopfian A) (hhopB : Kourovka.IsHopfian B)
    (f : A × B →* A × B) (hf : Function.Surjective f) : Function.Injective f :=
  Kourovka.problem_5_38 A B hfgA hfgB hsolA hsolB hhopA hhopB f hf


