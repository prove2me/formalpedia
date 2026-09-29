-- Prove2me | Definitions.Def_mme_dwz_table2_pair_coarsening
-- name    : mme_dwz_table2_pair_coarsening
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-25T12:34:54.145523+00:00
-- url     : https://prove2.me/theorems/5cb2ce1f-efd0-4aeb-99d5-cd1994fcf8d6
-- title:
--   DWZ Definition 6.4: coarsening a fine Z-pair by addition
-- statement:
--   A fine Z label in DWZ Definition 6.4 is a pair (r_left,r_right) with each coordinate in {0,1,2}. Define its coarse Z degree to be r_left+r_right, which lies in {0,1,2,3,4}. This is the exact coarsening map used to state that the typical pair histogram gamma has coarse marginal alpha_Z.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Definition 6.4 (printed p. 54 / PDF p. 55).

import Mathlib

set_option autoImplicit false

namespace MME.DWZTable2Counts

/-- The DWZ Definition 6.4 coarsening from a fine Z-pair to its coarse Z
degree.  Both fine degrees lie in `0,1,2`, so their sum lies in `Fin 5`. -/
def coarseOf (p : Fin 3 × Fin 3) : Fin 5 :=
  ⟨p.1.val + p.2.val, by omega⟩

end MME.DWZTable2Counts


