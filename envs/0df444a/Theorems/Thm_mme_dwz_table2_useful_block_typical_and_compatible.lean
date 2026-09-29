-- Prove2me | Theorems.Thm_mme_dwz_table2_useful_block_typical_and_compatible
-- name    : mme_dwz_table2_useful_block_typical_and_compatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T07:14:24.11129+00:00
-- url     : https://prove2.me/theorems/805f902c-8086-4f95-83ba-d0c52cb0e82a
-- title:
--   Every Table-2 useful small block is typical and compatible
-- statement:
--   Fix a Table-2 component word I and an available small Z-block z in the componentwise sense of Definitions 5.4 and 6.3. Then z has the exact global typical pair distribution gamma: $$|\{t:z_t=p\}|=\gamma(p)m \qquad \text{for every fine pair }p.$$ Moreover z satisfies every grouped compatibility cell used in Lemma 6.7 and Claim 6.8: boundary components remain separate, while interior components are grouped by their common coarse Z-grade. This theorem is the exact inclusion from the Hole Lemma's useful-block universe into the compatible typical-word space used for collision counting; it does not assert the converse.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Definitions 5.4, 6.1, 6.3, and 6.4 (PDF pp.47 and 51–53 / printed pp.46 and 50–52), specialized to Table 2.

import Definitions.Def_mme_dwz_table2_useful_block
import Theorems.Thm_mme_dwz_table2_useful_implies_compatible

open BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_useful_block_typical_and_compatible
    (m : ℕ) {Position : Type*} [Fintype Position]
    (outer : Position → Fin 15)
    (small : MME.DWZTable2StandardForm.UsefulBlock m outer) :
    (∀ p : Fin 3 × Fin 3,
      Fintype.card {t : Position // small.1 t = p} =
        MME.DWZTable2Counts.gamma p * m) ∧
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
            regionOfShape (outer t) = r ∧ (small.1 t).1 = a} =
        MME.DWZTable2Cardinality.cellCount m r a := by
  sorry
