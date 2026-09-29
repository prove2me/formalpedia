-- Prove2me | Theorems.Thm_mme_dwz_table2_fixed_outer_compatible_typical_equiv_split_assignments
-- name    : mme_dwz_table2_fixed_outer_compatible_typical_equiv_split_assignments
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T19:07:38.840189+00:00
-- url     : https://prove2.me/theorems/ffa17260-15b1-46c7-91fb-1ac3091aa937
-- title:
--   DWZ Equation (23): exact compatible fine words over a fixed outer word
-- statement:
--   Fix a scale multiplier $m$, a coarse $Z$-word $K$, and one literal Table-2 component word $I$ above $K$ having exactly the prescribed component histogram. Partition its positions into the regions used by Duan--Wu--Zhou conditions (a) and (c): boundary component types remain separate, while interior component types are grouped by their coarse $Z$-degree.
--
--   A fine word over $K$ is called typical when it has the exact Table-2 pair histogram $m\gamma$. It is compatible with $I$ when, in every region and for every left fine label, its regional incidence is the prescribed Table-2 cell count. Then there is an equivalence
--
--   $$
--   \{\text{typical fine words compatible with }I\}
--   \simeq \operatorname{SplitAssignments}(m).
--   $$
--
--   Consequently, every fixed Table-2 outer word has exactly the Equation-(23) family of compatible fine words. This supplies the fixed-row count needed for the finite incidence double count in Claim 6.8 and remains valid at $m=0$.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Definitions 6.4 and 6.6, Lemma 6.7, and Equations (22)--(23), printed pp. 53--56 (PDF pp. 54--57); https://arxiv.org/abs/2210.10173.

import Definitions.Def_mme_dwz_table2_split_assignments
import Definitions.Def_mme_dwz_table2_pair_coarsening

set_option autoImplicit false

theorem mme_dwz_table2_fixed_outer_compatible_typical_equiv_split_assignments
    (m : ℕ)
    {Position : Type*} [Fintype Position]
    (K : Position → Fin 5)
    (I : {w : Position → Fin 15 //
      (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
      ∀ s, Fintype.card {t : Position // w t = s} =
        MME.DWZTable2Counts.component s * m}) :
    let regionOfShape :
        Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
      if h : MME.DWZSquare.shapeX s = 0 ∨
          MME.DWZSquare.shapeY s = 0 then
        Sum.inl ⟨s, h⟩
      else
        Sum.inr (MME.DWZSquare.shapeZ s)
    let Typical :=
      {small : Position → Fin 3 × Fin 3 //
        (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
        ∀ p, Fintype.card {t : Position // small t = p} =
          MME.DWZTable2Counts.gamma p * m}
    let Compatible : Typical → Prop := fun small ↦
      ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
        Fintype.card
            {t : Position //
              regionOfShape (I.1 t) = r ∧ (small.1 t).1 = a} =
          MME.DWZTable2Cardinality.cellCount m r a
    Nonempty
      ({small : Typical // Compatible small} ≃
        MME.DWZTable2Cardinality.SplitAssignments m) := by
  sorry
