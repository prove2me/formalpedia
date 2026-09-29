-- Prove2me | Theorems.Thm_mme_dwz_q6_022_202_table2_scaled_rows_one_MM_restrict
-- name    : mme_dwz_q6_022_202_table2_scaled_rows_one_MM_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T06:54:12.925523+00:00
-- url     : https://prove2.me/theorems/bbb3a461-a610-40b8-9c2a-b110869c2c5d
-- title:
--   Exact one-MM restrictions for the 022/202 Table-2 rows
-- statement:
--   For every power multiplier $m$, let $D_m$ be the number of restricted $022$ words with the exact integral Table-2 parameters at scale $t=10366945m$. Then the row-$9$ restricted component power restricts to the matrix-multiplication tensor $MM(1,1,D_m)$, while the cyclic row-$10$ component restricts to $MM(D_m,1,1)$.
--
--   $$
--   MM(1,1,D_m) ≤_{res} T_9(m); MM(D_m,1,1) ≤_{res} T_{10}(m).
--   $$
--
--   This is the exact tensor-extraction interface needed before sixfold cyclic symmetrization; both orientations use the same canonical restricted-word cardinality.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Lemma 4.6 and the 022/202 restricted splitting used in Table 2.

import Definitions.Def_mme_dwz_table2_component_022_word_data
import Definitions.Def_mme_dwz_component_word_projection

open MME MME.DWZComponentRestriction
open MME.DWZTable2Component022

universe u

set_option autoImplicit false

theorem mme_dwz_q6_022_202_table2_scaled_rows_one_MM_restrict
    (K : Type u) [Field K] (m : ℕ) :
    let D := Nat.card (Restricted022Word 6
      (table2Power022 (10366945 * m))
      (table2OuterCount022 (10366945 * m))
      (table2MiddleCount022 (10366945 * m)))
    TensorObj.Restrict (MMObj K 1 1 D)
        (restrictedComponentPower K (9 : Fin 15) m) ∧
      TensorObj.Restrict (MMObj K D 1 1)
        (restrictedComponentPower K (10 : Fin 15) m) := by
  sorry
