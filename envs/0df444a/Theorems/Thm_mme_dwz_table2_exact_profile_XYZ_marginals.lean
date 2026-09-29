-- Prove2me | Theorems.Thm_mme_dwz_table2_exact_profile_XYZ_marginals
-- name    : mme_dwz_table2_exact_profile_XYZ_marginals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T01:23:57.040219+00:00
-- url     : https://prove2.me/theorems/9430831f-7311-430d-b934-6648e1d60d51
-- title:
--   Exact Table-2 joint profiles determine all three coarse marginals
-- statement:
--   Fix a finite word in the fifteen DWZ Table-2 component cells. Suppose cell $s$ occurs exactly $m c_s$ times, where $c_s$ is its prescribed integral Table-2 multiplicity. Then its coarse $X$, $Y$, and $Z$ histograms are the pushforwards of this joint profile:
--
--   $$
--   \#\{t:X(w_t)=x\}=\sum_{s:X(s)=x}m c_s,\qquad
--   \#\{t:Y(w_t)=y\}=\sum_{s:Y(s)=y}m c_s,
--   $$
--
--   and
--
--   $$
--   \#\{t:Z(w_t)=z\}=m\alpha_Z(z).
--   $$
--
--   This supplies the exact finite-histogram bridge from the fifteen-cell source profile to the three marginal families used by the DWZ first hash. It is valid for an arbitrary finite position type, including the empty type.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Table 2 (printed p. 59; PDF p. 60) and the Table-2 marginal setup in Sections 5–6; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_table2_exact_profile_coarse_Z_counts

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_exact_profile_XYZ_marginals
    (m : ℕ) {Position : Type*} [Fintype Position]
    (w : Position → Fin 15)
    (hw : ∀ s, Fintype.card {t : Position // w t = s} =
      MME.DWZTable2Counts.component s * m) :
    (∀ x, Fintype.card
        {t : Position // MME.DWZSquare.shapeX (w t) = x} =
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m) ∧
    (∀ y, Fintype.card
        {t : Position // MME.DWZSquare.shapeY (w t) = y} =
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
        MME.DWZTable2Counts.component s.1 * m) ∧
    ∀ z, Fintype.card
        {t : Position // MME.DWZSquare.shapeZ (w t) = z} =
      MME.DWZTable2Counts.alphaZ z * m := by
  sorry
