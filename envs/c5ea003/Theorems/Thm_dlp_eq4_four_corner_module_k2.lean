-- Prove2me | Theorems.Thm_dlp_eq4_four_corner_module_k2
-- name    : dlp_eq4_four_corner_module_k2
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T20:29:22.697426+00:00
-- url     : https://prove2.me/theorems/a93d9460-3731-4218-9234-39f73676e708
-- statement:
--   de la Pena-Montgomery-Smith (1995) sigma-randomization four-corner identity for k=2, stated over an arbitrary real module M (no normed structure required). For sign choices sigma_1, sigma_2 in {+1,-1} and copy indices l_1, l_2 in Fin 2, four times the value of f at the permuted copy pair equals the four-corner sigma-weighted sum sum_{j1,j2} (1 + cornerSign(j1,l1) sigma_1)(1 + cornerSign(j2,l2) sigma_2) f(j1,j2). This is the pure smul/add algebra underlying equation (4) of the de la Pena decoupling forward bound; the module-generic form is required because RealMatrix carries no NormedAddCommGroup instance so the normed-space abstract version cannot specialize to it.
-- source:
--   de la Pena, Montgomery-Smith, 'Decoupling inequalities for the tail probabilities of multivariate U-statistics', Ann. Probab. 23 (1995) 806-816 (arXiv:math/9309211), Section 4, equation (4) (k=2 case), p.811.

import Definitions.Def_dlp_sigma_randomization

open MatrixCompletion
open scoped BigOperators Classical

theorem dlp_eq4_four_corner_module_k2
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (σ₁ σ₂ : ℝ) (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (l₁ l₂ : Fin 2) (f : Fin 2 → Fin 2 → M) :
    (4 : ℝ) • f (dlpCopyPerm σ₁ l₁) (dlpCopyPerm σ₂ l₂)
      = ∑ j₁ : Fin 2, ∑ j₂ : Fin 2,
          ((1 + dlpCornerSign j₁ l₁ * σ₁) * (1 + dlpCornerSign j₂ l₂ * σ₂)) •
            f j₁ j₂ := by sorry
