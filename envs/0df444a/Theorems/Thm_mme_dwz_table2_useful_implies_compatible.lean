-- Prove2me | Theorems.Thm_mme_dwz_table2_useful_implies_compatible
-- name    : mme_dwz_table2_useful_implies_compatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T21:09:12.715141+00:00
-- url     : https://prove2.me/theorems/e44cd1ed-e5f0-4b74-9d08-c9b2f94b5e77
-- title:
--   DWZ Table 2: usefulness implies compatibility
-- statement:
--   Fix an exact Table-2 multiplier m, a word of the fifteen large component shapes, and a word of fine Z split pairs. Assume that, separately inside every large component s and for each left split label a, the fine word has exactly split(s,a)·m occurrences. Then after sending every boundary component (X-degree zero or Y-degree zero) to its own region and grouping all remaining components by coarse Z degree, every regional left-label fiber has exactly the prescribed Table-2 cellCount(m,r,a). This is the exact finite implication from the componentwise split condition in DWZ Definition 6.3 (usefulness) to the grouped compatibility predicate used by the formal Claim-6.8 interfaces. The premise contains no regional compatibility equation, tensor-support assertion, hash collision, or hole certificate.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.1: Definition 6.1, Claim 6.2, Definition 6.3, and Additional Zeroing-Out Steps 1-2.

import Definitions.Def_mme_dwz_table2_split_assignments

set_option autoImplicit false

theorem mme_dwz_table2_useful_implies_compatible
    (m : ℕ)
    {Position : Type*} [Fintype Position]
    (outer : Position → Fin 15)
    (small : Position → Fin 3 × Fin 3)
    (hUseful : ∀ (s : Fin 15) (a : Fin 3),
      Fintype.card
          {t : Position // outer t = s ∧ (small t).1 = a} =
        MME.DWZTable2Counts.split s a * m) :
    let regionOfShape :
        Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
      if h : MME.DWZSquare.shapeX s = 0 ∨
          MME.DWZSquare.shapeY s = 0 then
        Sum.inl ⟨s, h⟩
      else
        Sum.inr (MME.DWZSquare.shapeZ s)
    ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
      Fintype.card
          {t : Position //
            regionOfShape (outer t) = r ∧ (small t).1 = a} =
        MME.DWZTable2Cardinality.cellCount m r a := by
  sorry
