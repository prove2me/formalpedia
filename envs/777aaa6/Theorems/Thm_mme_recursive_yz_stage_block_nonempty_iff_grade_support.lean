-- Prove2me | Theorems.Thm_mme_recursive_yz_stage_block_nonempty_iff_grade_support
-- name    : mme_recursive_yz_stage_block_nonempty_iff_grade_support
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T09:52:17.666853+00:00
-- url     : https://prove2.me/theorems/33000da2-00c1-4fa8-9361-2bca240decec
-- title:
--   Stage profile-block feasibility is equivalent to grade support
-- statement:
--   Let $A$ be a recursive Y/Z stage and fix one of its three modes $i$. For a coarse cell $d$, write $s_i(d)$ for the prescribed grade and $\mu_i(d,w)$ for its complete-word histogram. The stage's intact mode block is nonempty if and only if
--
--   $$
--   \mu_i(d,w)>0\quad\Longrightarrow\quad\sum_r w_r=s_i(d)
--   $$
--
--   for every cell $d$ and complete word $w$. The entries $w_r$ are the elementary grades $0,1,2$. The stage certificate already supplies the required cellwise mass identities, so no additional mass hypothesis is needed. This characterizes existence of a valid mode-word assignment; it does not assert that the intact tensor is nonzero.
-- source:
--   Direct finite histogram realization for RecursiveYZ.CellWord and the mass/reference-target fields of RecursiveYZ.Certificate.Stage.

import Definitions.Def_mme_recursive_yz_stage_certificate
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.BigOperators

open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.Certificate MME.CompleteSplit

theorem mme_recursive_yz_stage_block_nonempty_iff_grade_support
    {D : HashExtraction.HashData} (A : Stage D) (i : Fin 3) :
    Nonempty (CWCells.Block A.ell (fullCell A.total A.reference)
      (fun c i => (c.2.val i).val) A.mu i) ↔
    ∀ c w, 0 < A.mu i c w → CWCells.grade w = (c.2.val i).val := by sorry
