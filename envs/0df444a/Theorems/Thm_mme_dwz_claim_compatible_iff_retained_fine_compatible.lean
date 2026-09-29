-- Prove2me | Theorems.Thm_mme_dwz_claim_compatible_iff_retained_fine_compatible
-- name    : mme_dwz_claim_compatible_iff_retained_fine_compatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T12:12:55.302165+00:00
-- url     : https://prove2.me/theorems/17dfbaf4-ebd1-48ef-8663-d9eb3b8eb508
-- title:
--   Claim-6.8 compatibility equals encoded fine-address compatibility
-- statement:
--   Fix a retained Table-2 outer-word family, a useful fine-$Z$ pair word $z$ owned by one copy, and an auxiliary pair word $z'$ with the same underlying function. For any retained copy $j$, the Claim-6.8 grouped compatibility equations for $z'$ hold if and only if the encoded fine-nine address of $z$ satisfies the Step-2 address compatibility predicate with $j$:
--
--   $$
--   \operatorname{Compatible}_{\mathrm{Claim6.8}}(j,z')
--   \quad\Longleftrightarrow\quad
--   \operatorname{Compatible}_{\mathrm{address}}(\operatorname{encode}(z),j).
--   $$
--
--   Both sides assert the same exact cardinality in every boundary or interior split region and every left fine grade, including zero cells and empty position types. This equivalence connects the compatibility relation used by the collision-fiber broken copy to the relation used by the tensor restriction.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, conditions (a) and (c), Definition 6.3, and Claim 6.8, printed pp. 50-57 (PDF pp. 51-58); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_useful_block
import Definitions.Def_mme_dwz_retained_fine_compatibility

open MME
open MME.DWZStep1Support
open MME.DWZStep2Source

universe u v

set_option autoImplicit false

theorem mme_dwz_claim_compatible_iff_retained_fine_compatible
    (m : ℕ) {Copy : Type v} {Position : Type u} [Fintype Position]
    (outer : Copy → Position → Fin 15)
    {owner : Copy}
    (small : MME.DWZTable2StandardForm.UsefulBlock m (outer owner))
    (smallWord : Position → Fin 3 × Fin 3)
    (hSmallWord : smallWord = small.1)
    (j : Copy) :
    (let regionOfShape :
        Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
      if h : MME.DWZSquare.shapeX s = 0 ∨
          MME.DWZSquare.shapeY s = 0 then
        Sum.inl ⟨s, h⟩
      else
        Sum.inr (MME.DWZSquare.shapeZ s)
    ∀ (region : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
      Fintype.card
          {t : Position //
            regionOfShape (outer j t) = region ∧ (smallWord t).1 = a} =
        MME.DWZTable2Cardinality.cellCount m region a) ↔
      retainedFineCompatible m outer
        (fun t ↦ fineSplitGrade (small.1 t).1 (small.1 t).2) j := by
  sorry
