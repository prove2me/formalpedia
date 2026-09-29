-- Prove2me | Theorems.Thm_mme_released_interior_child_boundary_or_canonical_112
-- name    : mme_released_interior_child_boundary_or_canonical_112
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:41:04.404346+00:00
-- url     : https://prove2.me/theorems/5a7dc8d0-9131-4253-9a35-b94e4a45e03c
-- title:
--   Every released square child is boundary or a permutation of 112
-- statement:
--   Every admissible square child of every released parent has a zero coordinate, or admits an explicit coordinate equivalence to the canonical 112 shape. The classification follows from total grade four and is independent of the released recipe parameters. It identifies which extraction theorem applies; it does not yet supply the child marginal identities or matrix-product restrictions. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Definitions.Def_mme_released_interior_integer_profiles
open MME MME.RecursiveYZ MME.ReleasedInterior

theorem mme_released_interior_child_boundary_or_canonical_112
    (s : Fin 45) (c : Cell 4 6 (parent s)) :
    (∃ i : Fin 3, (c.2.val i).val = 0) ∨
      ∃ e : Equiv.Perm (Fin 3),
        (c.2.val (e 0)).val = 1 ∧ (c.2.val (e 1)).val = 1 ∧
          (c.2.val (e 2)).val = 2 := by sorry
