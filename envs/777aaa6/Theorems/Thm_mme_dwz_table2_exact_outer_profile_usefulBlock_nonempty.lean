-- Prove2me | Theorems.Thm_mme_dwz_table2_exact_outer_profile_usefulBlock_nonempty
-- name    : mme_dwz_table2_exact_outer_profile_usefulBlock_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T11:31:19.245138+00:00
-- url     : https://prove2.me/theorems/a958bd5b-1cec-4fa3-a598-670b3340f794
-- title:
--   Every exact Table-2 outer profile has a literal useful fine-Z block
-- statement:
--   Let a finite position set carry an outer Table-2 component word in which component $s$ occurs exactly $m c_s$ times, where $c_s$ is the exact integer Table-2 component count. Then there exists a literal useful fine-$Z$ word over these same positions: every fine pair coarsens to the outer $Z$ degree, and for every component $s$ and left grade $a$, exactly $m c_{s,a}$ positions have that pair of labels, where $c_{s,a}$ is the exact Table-2 split count.
--
--   The result constructs the actual useful-block type needed by Claim 6.8, rather than proving only a cardinality surrogate. It is valid for $m=0$ and permits zero cells in the split table.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 6.3 and Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_useful_block
import Theorems.Thm_mme_dwz_table2_integer_counts_exact
import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_nonempty

open BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_exact_outer_profile_usefulBlock_nonempty
    (m : ℕ) {Position : Type*}
    [Fintype Position] [DecidableEq Position]
    (outer : Position → Fin 15)
    (hProfile : ∀ s : Fin 15,
      Fintype.card {t : Position // outer t = s} =
        MME.DWZTable2Counts.component s * m) :
    Nonempty (MME.DWZTable2StandardForm.UsefulBlock m outer) := by
  sorry
