-- Prove2me | Theorems.Thm_mme_dwz_table2_regional_splits_aggregate_gamma
-- name    : mme_dwz_table2_regional_splits_aggregate_gamma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T13:28:27.040797+00:00
-- url     : https://prove2.me/theorems/9692e19a-5c93-4bcb-bde0-26be5e65fdcb
-- title:
--   DWZ Table 2 regional split counts aggregate to gamma
-- statement:
--   For every fine pair $p=(r_\ell,r_r)$ in the exact integral DWZ Table-2 data,
--   let $k=r_\ell+r_r$.  Sum the prescribed $r_\ell$-cell counts over all boundary
--   components of coarse $Z$-degree $k$, and add the corresponding interior
--   $(+,+,k)$ cell count.  The result is exactly the stored global typical-pair
--   count $\gamma(p)$:
--
--   $$
--   \sum_{\substack{s:\,x(s)=0\ \mathrm{or}\ y(s)=0\\z(s)=k}}
--     \operatorname{split}(s,r_\ell)
--   +\operatorname{plusSplit}(k,r_\ell)=\gamma(r_\ell,r_r).
--   $$
--
--   This exact nine-cell identity is the arithmetic hinge that lets the disjoint
--   regional numerator assignments glue into a globally typical fine word in
--   DWZ Lemma 6.7.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, arXiv:2210.10173, proof of Lemma 6.7 and Equation (23), printed pp. 54–56; exact q=6 square data from Section 6.3 Table 2.

import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_table2_pair_coarsening

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_regional_splits_aggregate_gamma
    (p : Fin 3 × Fin 3) :
    (∑ s : Fin 15,
      if (MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0) ∧
          MME.DWZSquare.shapeZ s = MME.DWZTable2Counts.coarseOf p then
        MME.DWZTable2Counts.split s p.1
      else 0) +
      MME.DWZTable2Counts.plusSplit
        (MME.DWZTable2Counts.coarseOf p) p.1 =
      MME.DWZTable2Counts.gamma p := by sorry
