-- Prove2me | Theorems.Thm_mme_dwz_table2_compatible_outer_candidate_count_upper
-- name    : mme_dwz_table2_compatible_outer_candidate_count_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T19:47:31.753911+00:00
-- url     : https://prove2.me/theorems/0e92c07f-07b3-4b17-9464-aafffe0f2ee2
-- title:
--   DWZ Claim 6.8: finite upper bound for compatible outer candidates
-- statement:
--   Fix an integral Table-2 scale multiplier $m$, a coarse $Z$-word $K$ with exact histogram $m\alpha_Z$, and a chosen typical fine word $s_0$ above $K$. Let $\mathcal O_K$ be the literal Table-2 outer words above $K$, and let compatibility mean the exact disjoint regional split conditions (a) and (c) preceding DWZ Equation (23). Then\n\n$$\n|\{I\in\mathcal O_K:I\sim s_0\}|\n\leq (6(10^{16}m+1))^9\,|\mathcal O_K|\,\exp\!\bigl(m\,10^{16}\log 2\,\log_2\alpha_P\bigr).\n$$\n\nThis is the complementary finite upper direction for Lemma 6.7. It bounds the exact $(N_\alpha/N_{B_Z})p_{\mathrm{comp}}$ candidate term used to choose the modulus in Claim 6.8. The theorem is division-free, includes $m=0$, and explicitly exposes the sole degree-nine method-of-types loss.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Definition 6.6, Lemma 6.7, Equations (22)--(23), and Claim 6.8, printed pp. 54--57 (PDF pp. 55--58); https://arxiv.org/abs/2210.10173.

import Theorems.Thm_mme_dwz_lemma6_7_typical_denominator_count
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_multinomial_entropy_upper
import Theorems.Thm_mme_dwz_table2_equation23_numerator_count
import Theorems.Thm_mme_dwz_table2_gamma_pushforward
import Theorems.Thm_mme_dwz_table2_integer_counts_exact
import Theorems.Thm_mme_dwz_table2_logAlphaP_integer_identity
import Theorems.Thm_mme_dwz_table2_compatible_incidence_factorization

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_compatible_outer_candidate_count_upper
    (m : ℕ)
    {Position : Type*} [Fintype Position] [DecidableEq Position]
    (K : Position → Fin 5)
    (hK : ∀ k, Fintype.card {t : Position // K t = k} =
      MME.DWZTable2Counts.alphaZ k * m) :
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
      (Nat.card {I : Outer // Compatible I small₀} : ℝ) ≤
        (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 9 *
          (Nat.card Outer : ℝ) *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              MME.DWZSquare.logAlphaP) := by
  sorry
