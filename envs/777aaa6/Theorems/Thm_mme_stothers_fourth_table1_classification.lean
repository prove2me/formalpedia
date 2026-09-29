-- Prove2me | Theorems.Thm_mme_stothers_fourth_table1_classification
-- name    : mme_stothers_fourth_table1_classification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T18:55:36.149574+00:00
-- url     : https://prove2.me/theorems/3e9b9bf0-ea98-4beb-84ca-f22e9cb60283
-- title:
--   The 45 fourth-power blocks and ten Table-1 classes
-- statement:
--   Among ordered triples $(i,j,k)\in\{0,\ldots,8\}^3$, exactly 45 satisfy $i+j+k=8$. Every such triple belongs to a unique coordinate-permutation orbit represented by one of
--
--   $$
--   008,017,026,035,044,116,125,134,224,233.
--   $$
--
--   The orbit of representative $r$ has cardinality $3n_r$, where the Table-1 multiplicities are $n=(1,2,2,2,1,1,2,2,1,1)$. This is the finite classification used to group the 45 fourth-power constituents into ten cyclic symmetry classes.
-- source:
--   Davie and Stothers (2013), Section 5 and Table 1, printed pp. 363 and 367, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_fourth_data

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_fourth_table1_classification :
    Fintype.card
        {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8} = 45 ∧
    (∀ sigma : {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8},
      ∃! r : Fin 10,
        MME.StothersFourth.sameOrbit sigma.1
          (MME.StothersFourth.classRep r)) ∧
    (∀ r : Fin 10,
      Fintype.card
          {sigma : {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8} //
            MME.StothersFourth.sameOrbit sigma.1
              (MME.StothersFourth.classRep r)} =
        3 * MME.StothersFourth.classMultiplicity r) := by
  sorry
