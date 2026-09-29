-- Prove2me | Theorems.Thm_mme_dwz_table2_component_words_supply_outer_layout
-- name    : mme_dwz_table2_component_words_supply_outer_layout
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T15:22:27.31079+00:00
-- url     : https://prove2.me/theorems/4b0cd8a3-a4f2-4beb-822a-f27128273339
-- title:
--   Exact Table-2 component words supply the fourteen regional layouts
-- statement:
--   Fix an integral multiplier $m$, a finite set of literal positions, and a
--   coarse word $K$ on those positions.  Suppose that every outer object carries a
--   Table-2 component word whose fiber over each of the fifteen component shapes
--   $s$ has exactly
--
--   $$
--   \operatorname{component}(s)\,m
--   $$
--
--   positions, and whose component Z-degree agrees pointwise with $K$.
--
--   Partition that word exactly as in conditions (a) and (c) preceding DWZ
--   Equation (23): retain every boundary component ($i=0$ or $j=0$) as its own
--   region, and group every interior component by its coarse Z-degree $k$.  Then
--   for every outer object there is a bijection from the canonical disjoint union
--   of Table-2 regional position types to the literal position set, and this
--   bijection preserves the coarse degree pointwise.
--
--   The statement includes $m=0$.  If an outer object exists, its exact
--   component-fiber hypotheses force the literal position set to be empty and the
--   construction supplies the unique empty layout.  If the outer family itself is
--   empty, the requested family of layouts and its preservation condition are
--   both vacuous.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Lemma 6.7 conditions (a) and (c) and Equation (23), printed pp. 54--56 (PDF pp. 55--57), specialized to the exact q=6 component distribution in Section 6.3 and Table 2, printed p. 59 (PDF p. 60); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_split_assignments

set_option autoImplicit false

theorem mme_dwz_table2_component_words_supply_outer_layout
    (m : ℕ)
    {Outer Position : Type*}
    [Finite Outer] [Fintype Position]
    (K : Position → Fin 5)
    (shapeWord : Outer → Position → Fin 15)
    (hshape : ∀ (I : Outer) (s : Fin 15),
      Fintype.card {t : Position // shapeWord I t = s} =
        MME.DWZTable2Counts.component s * m)
    (hmatch : ∀ (I : Outer) (t : Position),
      MME.DWZSquare.shapeZ (shapeWord I t) = K t) :
    ∃ layout : ∀ _I : Outer,
        (Σ r : MME.DWZTable2Cardinality.SplitRegion,
          MME.DWZTable2Cardinality.RegionPosition m r) ≃ Position,
      ∀ (I : Outer)
          (x : Σ r : MME.DWZTable2Cardinality.SplitRegion,
            MME.DWZTable2Cardinality.RegionPosition m r),
        K (layout I x) =
          MME.DWZTable2Cardinality.coarseDegree x.1 := by
  sorry
