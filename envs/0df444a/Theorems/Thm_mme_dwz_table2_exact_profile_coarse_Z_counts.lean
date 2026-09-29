-- Prove2me | Theorems.Thm_mme_dwz_table2_exact_profile_coarse_Z_counts
-- name    : mme_dwz_table2_exact_profile_coarse_Z_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T22:55:11.095741+00:00
-- url     : https://prove2.me/theorems/c5666df6-4416-4df1-9b62-0240e2e4ec42
-- title:
--   Exact Table-2 component profiles push forward to the coarse-Z profile
-- statement:
--   Let $w$ label a finite set of positions by the fifteen joint Table-2 component shapes, and suppose shape $s$ occurs exactly $m c_s$ times. Then every coarse $Z$-shape $z$ occurs exactly $m\alpha^Z_z$ times:
--
--   $$\#\{t:\operatorname{shape}_Z(w_t)=z\}=m\alpha^Z_z.$$
--
--   This is the histogram transport needed to compare the fixed-coarse-$Z$ competitor spaces attached to different owners in the global exact-profile family.
-- source:
--   Duan--Wu--Zhou Table-2 integer component and marginal identities.

import Theorems.Thm_mme_dwz_table2_integer_counts_exact

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_exact_profile_coarse_Z_counts
    (m : ℕ) {Position : Type*} [Fintype Position]
    (w : Position → Fin 15)
    (hw : ∀ s, Fintype.card {t : Position // w t = s} =
      MME.DWZTable2Counts.component s * m) :
    ∀ z, Fintype.card
        {t : Position // MME.DWZSquare.shapeZ (w t) = z} =
      MME.DWZTable2Counts.alphaZ z * m := by
  sorry
