-- Prove2me | Theorems.Thm_dlp_eq4_eight_corner_randomization_order3
-- name    : dlp_eq4_eight_corner_randomization_order3
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-23T20:57:28.811001+00:00
-- url     : https://prove2.me/theorems/1cbd2551-5bf0-4e35-abc6-a96628f56782
-- title:
--   de la Peña–Montgomery-Smith eq. (4): eight-corner randomization, order 3
-- statement:
--   de la Peña–Montgomery-Smith eq (4)/(3), order-3 (k=3) eight-corner sigma-randomization. For three independent symmetric sign variables sigma_1,sigma_2,sigma_3 in {1,-1} and target superscripts l_1,l_2,l_3, the value 8 * f(copyPerm sigma_1 l_1, copyPerm sigma_2 l_2, copyPerm sigma_3 l_3) equals the 8-term sum over j_1,j_2,j_3 in Fin 2 of the product of corner factors (1 + cornerSign(j_r,l_r)*sigma_r) applied to f(j_1,j_2,j_3). The factor (1+cornerSign(j,l)*sigma) equals 2 when copyPerm sigma l = j and 0 otherwise, so the triple product collapses the 8 corners onto the single surviving corner with weight 2*2*2=8. Order-3 mirror of the order-2 four-corner randomization dlp_eq4_four_corner_randomization_k2 (f431d4a8).
-- source:
--   de la Peña, Montgomery-Smith, 'Decoupling inequalities for the tail probabilities of multivariate U-statistics', Ann. Probab. 23 (1995) 806-816 (arXiv:math/9309211), Section 4, eq (3) explicit k=3 8-term expansion lines 311-321, eq (4) general-k lines 405-422. O'Donnell, Analysis of Boolean Functions, Section 9.1.

import Definitions.Def_dlp_sigma_randomization
open MatrixCompletion
open scoped BigOperators Classical

theorem dlp_eq4_eight_corner_randomization_order3
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (σ₁ σ₂ σ₃ : ℝ) (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hσ₃ : σ₃ = 1 ∨ σ₃ = -1)
    (l₁ l₂ l₃ : Fin 2) (f : Fin 2 → Fin 2 → Fin 2 → V) :
    (8 : ℝ) • f (dlpCopyPerm σ₁ l₁) (dlpCopyPerm σ₂ l₂) (dlpCopyPerm σ₃ l₃)
      = ∑ j₁ : Fin 2, ∑ j₂ : Fin 2, ∑ j₃ : Fin 2,
          ((1 + dlpCornerSign j₁ l₁ * σ₁) * (1 + dlpCornerSign j₂ l₂ * σ₂)
            * (1 + dlpCornerSign j₃ l₃ * σ₃))
            • f j₁ j₂ j₃ := by
  sorry
