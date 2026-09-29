-- Prove2me | Theorems.Thm_mme_dwz_table2_fixed_small_compatible_outer_card_eq
-- name    : mme_dwz_table2_fixed_small_compatible_outer_card_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T18:43:12.130131+00:00
-- url     : https://prove2.me/theorems/6ececc43-ee37-4317-a89f-5661fa7a3514
-- title:
--   DWZ Lemma 6.7: pointwise symmetry of fixed-small compatible outer words
-- statement:
--   Fix a coarse word $K$ and the exact integral Table-2 data at multiplier $m$. Let $\mathcal O_K$ be the family of all matchable fifteen-component outer words over $K$, and let $\mathcal T_K$ be the family of all typical fine $Z$-words with histogram $m\gamma$. An outer word $I$ is compatible with a fine word $b$ when every boundary component and every aggregated interior region $(+,+,k)$ has the exact left-split cell counts prescribed by conditions (a) and (c) before Equation (23). Then for every $b_1,b_2\in\mathcal T_K$,
--
--   $$
--   \#\{I\in\mathcal O_K:I\text{ is compatible with }b_1\}
--   =\#\{I\in\mathcal O_K:I\text{ is compatible with }b_2\}.
--   $$
--
--   Thus the number of compatible matchable outer words is pointwise independent of the chosen typical small block, formalizing the symmetry invoked in Definition 6.6 and Lemma 6.7. This is the pointwise form required by Claim 6.8; it does not yet assert the numerical value of the common cardinality or a hashing-survival bound.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Definition 6.4, Definition 6.6, Lemma 6.7, Equations (22)-(23), and Claim 6.8 (printed pp. 54-57, PDF pp. 55-58); https://arxiv.org/abs/2210.10173.

import Definitions.Def_mme_dwz_table2_split_assignments
import Definitions.Def_mme_dwz_table2_pair_coarsening

set_option autoImplicit false

theorem mme_dwz_table2_fixed_small_compatible_outer_card_eq
    (m : ℕ)
    {Position : Type*} [Fintype Position] [DecidableEq Position]
    (K : Position → Fin 5) :
    let regionOfShape :
        Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
      if h : MME.DWZSquare.shapeX s = 0 ∨
          MME.DWZSquare.shapeY s = 0 then
        Sum.inl ⟨s, h⟩
      else
        Sum.inr (MME.DWZSquare.shapeZ s)
    let Outer :=
      {w : Position → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
        ∀ s, Fintype.card {t : Position // w t = s} =
          MME.DWZTable2Counts.component s * m}
    let Typical :=
      {small : Position → Fin 3 × Fin 3 //
        (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
        ∀ p, Fintype.card {t : Position // small t = p} =
          MME.DWZTable2Counts.gamma p * m}
    let Compatible : Outer → Typical → Prop := fun I small ↦
      ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
        Fintype.card
            {t : Position //
              regionOfShape (I.1 t) = r ∧ (small.1 t).1 = a} =
          MME.DWZTable2Cardinality.cellCount m r a
    ∀ small₁ small₂ : Typical,
      Nat.card {I : Outer // Compatible I small₁} =
        Nat.card {I : Outer // Compatible I small₂} := by sorry
