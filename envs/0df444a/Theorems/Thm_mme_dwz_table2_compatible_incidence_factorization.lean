-- Prove2me | Theorems.Thm_mme_dwz_table2_compatible_incidence_factorization
-- name    : mme_dwz_table2_compatible_incidence_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T19:20:39.89334+00:00
-- url     : https://prove2.me/theorems/8dd9a3b6-1f22-473f-aa3a-5aa1ba4f41b4
-- title:
--   DWZ Table 2: exact compatibility-incidence factorization
-- statement:
--   Fix a scale multiplier $m$, a coarse $Z$-word $K$, and a typical fine word $s_0$ above it. Let $\mathcal O_K$ be the literal Table-2 component words above $K$, let $\mathcal T_K$ be the typical fine words with histogram $m\gamma$, and let $I\sim s$ mean that the pair satisfies the exact regional split conditions (a) and (c). Then
--
--   $$
--   |\mathcal T_K|\,|\{I\in\mathcal O_K:I\sim s_0\}|
--   =|\mathcal O_K|\,|\operatorname{SplitAssignments}(m)|.
--   $$
--
--   This is the division-free double count of the finite compatibility incidence relation. The left factorization uses the fact that every typical fine word has the same compatible-outer fiber size, while the right factorization uses the exact Equation-(23) row count. It introduces no positivity, cancellation, or natural-number division assumption and remains valid for $m=0$.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Definition 6.6, Lemma 6.7, Equations (22)--(23), and the compatible-candidate term in Claim 6.8, printed pp. 53--57 (PDF pp. 54--58); https://arxiv.org/abs/2210.10173.

import Theorems.Thm_mme_dwz_table2_fixed_small_compatible_outer_card_eq
import Theorems.Thm_mme_dwz_table2_fixed_outer_compatible_typical_equiv_split_assignments

set_option autoImplicit false

theorem mme_dwz_table2_compatible_incidence_factorization
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
    ∀ small₀ : Typical,
      Nat.card Typical *
          Nat.card {I : Outer // Compatible I small₀} =
        Nat.card Outer *
          Nat.card (MME.DWZTable2Cardinality.SplitAssignments m) := by
  sorry
