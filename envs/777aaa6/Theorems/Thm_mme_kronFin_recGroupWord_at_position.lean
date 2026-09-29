-- Prove2me | Theorems.Thm_mme_kronFin_recGroupWord_at_position
-- name    : mme_kronFin_recGroupWord_at_position
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T08:42:05.766813+00:00
-- url     : https://prove2.me/theorems/c82116df-68f8-4826-83ed-dc3f09de6192
-- title:
--   Recursive grouped words recover the exact flat letter at every position
-- statement:
--   Partition a flat dependent word into $k$ consecutive fibers of lengths $c_s$. For every grouped position $(s,r)$, the letter returned by recursive regrouping is exactly the original flat letter at the inverse image of $(s,r)$ under the canonical position equivalence. The equality is heterogeneous because the letter type may depend on the fiber label.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.2--5.5 (regrouping component-word positions), https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_kronFin_rec_group_position_equiv_data

open MME

universe u

set_option autoImplicit false

theorem mme_kronFin_recGroupWord_at_position
    {k : ℕ} {count : Fin k → ℕ} {index : Fin k → Type u}
    (w : ∀ r, TensorObj.recGroupFamily k count index r)
    (p : Σ s, Fin (count s)) :
    HEq (TensorObj.recGroupWord w p.1 p.2)
      (w ((TensorObj.recGroupPositionEquiv k count).symm p)) := by
  sorry
