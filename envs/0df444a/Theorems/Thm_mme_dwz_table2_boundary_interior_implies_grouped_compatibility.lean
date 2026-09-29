-- Prove2me | Theorems.Thm_mme_dwz_table2_boundary_interior_implies_grouped_compatibility
-- name    : mme_dwz_table2_boundary_interior_implies_grouped_compatibility
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T05:56:05.781129+00:00
-- url     : https://prove2.me/theorems/1fb86680-fb26-4c95-aac5-376a955cec04
-- title:
--   Boundary and interior Step-1 histograms give the exact grouped compatibility cells
-- statement:
--   Partition the fifteen Table-2 components into the disjoint regional form of DWZ compatibility: every boundary component remains a separate region, while all interior components with the same coarse $Z$-grade $k$ form the region $(+,+,k)$. If every boundary component has its exact split histogram and every interior $k$-region has its exact `plusSplit` histogram, then for every grouped region $r$ and fine left grade $a$,
--
--   $$
--   \#\{t:\operatorname{region}(\operatorname{outer}(t))=r,\;z_L(t)=a\}
--   =\operatorname{cellCount}(m,r,a).
--   $$
--
--   This is the exact finite compatibility conclusion needed after Additional Zeroing-Out Step 1; no componentwise interior histogram is assumed.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Definitions 6.1 and 6.3, Claim 6.2, and Additional Zeroing-Out Step 1. https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_step1_z_histogram_fibers

open MME MME.DWZStep1Histogram

set_option autoImplicit false

theorem mme_dwz_table2_boundary_interior_implies_grouped_compatibility
    (m : ℕ)
    {Position : Type*} [Fintype Position]
    (outer : Position → Fin 15) (zLeft : Position → Fin 3)
    (hBoundary : ∀ (s : Fin 15),
      MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 →
      ∀ a : Fin 3,
        Fintype.card (ComponentZFiber outer zLeft s a) =
          MME.DWZTable2Counts.split s a * m)
    (hInterior : ∀ (k : Fin 5) (a : Fin 3),
      Fintype.card (InteriorZFiber outer zLeft k a) =
        MME.DWZTable2Counts.plusSplit k a * m) :
    let groupedRegion :
        Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s =>
      if h : MME.DWZSquare.shapeX s = 0 ∨
          MME.DWZSquare.shapeY s = 0 then
        Sum.inl ⟨s, h⟩
      else
        Sum.inr (MME.DWZSquare.shapeZ s)
    ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
      Fintype.card
          {t : Position // groupedRegion (outer t) = r ∧ zLeft t = a} =
        MME.DWZTable2Cardinality.cellCount m r a := by
  sorry
