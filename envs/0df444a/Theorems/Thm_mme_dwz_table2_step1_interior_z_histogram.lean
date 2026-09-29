-- Prove2me | Theorems.Thm_mme_dwz_table2_step1_interior_z_histogram
-- name    : mme_dwz_table2_step1_interior_z_histogram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T05:50:17.598274+00:00
-- url     : https://prove2.me/theorems/374aa37d-3a4c-4926-944c-48189cee30b4
-- title:
--   DWZ Step 1: total and boundary Z-histograms force the interior histogram
-- statement:
--   Fix a coarse $Z$-grade $k$ and a left fine grade $a$. Suppose the total number of positions with these grades is the prescribed total split count times $m$, and every boundary component already has its prescribed split histogram. Then the remaining positions—those in the unique interior component with both coarse $X$- and $Y$-grades nonzero—have cardinality
--
--   $$
--   \# I_{k,a}=\operatorname{plusSplit}(k,a)\,m.
--   $$
--
--   The proof is an exact finite partition of the total fibre into boundary fibres and the interior fibre, followed by the Table-2 conservation identity. This is the interior half of Additional Zeroing-Out Step 1.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 6.1, Claim 6.2 and Additional Zeroing-Out Step 1 (printed pp. 51--52 / PDF pp. 52--53). https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_table2_total_z_split_balance

open BigOperators
open MME MME.DWZStep1Histogram

set_option autoImplicit false

theorem mme_dwz_table2_step1_interior_z_histogram
    (m : ℕ)
    {Position : Type*} [Fintype Position]
    (outer : Position → Fin 15) (zLeft : Position → Fin 3)
    (hTotal : ∀ (k : Fin 5) (a : Fin 3),
      Fintype.card (TotalZFiber outer zLeft k a) =
        table2TotalZSplit k a * m)
    (hBoundary : ∀ (s : Fin 15),
      MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 →
      ∀ a : Fin 3,
        Fintype.card (ComponentZFiber outer zLeft s a) =
          MME.DWZTable2Counts.split s a * m) :
    ∀ (k : Fin 5) (a : Fin 3),
      Fintype.card (InteriorZFiber outer zLeft k a) =
        MME.DWZTable2Counts.plusSplit k a * m := by
  sorry
