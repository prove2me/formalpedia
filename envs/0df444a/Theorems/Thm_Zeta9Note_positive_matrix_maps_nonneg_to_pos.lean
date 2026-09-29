-- Prove2me | Theorems.Thm_Zeta9Note_positive_matrix_maps_nonneg_to_pos
-- name    : Zeta9Note.positive_matrix_maps_nonneg_to_pos
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T07:31:27.691979+00:00
-- url     : https://prove2.me/theorems/1aea0d88-d250-4dd6-875b-679c2aefdc90
-- title:
--   Entrywise positive matrices send nonzero nonnegative vectors to positive vectors
-- statement:
--   Let M be a 5×5 real matrix all of whose entries are strictly positive, and let v be a nonzero vector with nonnegative entries. Then every entry of M v is strictly positive.
-- source:
--   Abstract layer distilled from the v0.1 research note (Zenodo 10.5281/zenodo.22951155); statement and proof in formalization/Zeta9Note.lean.

import Mathlib

namespace Zeta9Note

theorem positive_matrix_maps_nonneg_to_pos
    (M : Matrix (Fin 5) (Fin 5) ℝ) (hM : ∀ i j : Fin 5, 0 < M i j)
    (v : Fin 5 → ℝ) (hv : v ≠ 0) (hvnn : ∀ i : Fin 5, 0 ≤ v i) :
    ∀ i : Fin 5, 0 < M.mulVec v i := by sorry

end Zeta9Note
