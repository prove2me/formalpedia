-- Prove2me | Theorems.Thm_mme_dwz_fourth_canonical_support_square_pairs
-- name    : mme_dwz_fourth_canonical_support_square_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T15:20:58.252868+00:00
-- url     : https://prove2.me/theorems/8f51f08b-c1c9-4f07-b9c6-ebd4a074d226
-- title:
--   Fourth CW support is the coordinatewise sum of two square shapes
-- statement:
--   Let $K$ be any field and let $q>0$. Enumerate the fifteen supported square-component grades as $g_0,\ldots,g_{14}$, in the existing DWZ Table 2 order, and let $\sigma\in\{0,\ldots,8\}^3$ be a grade of the canonical fourth-power tensor. Then
--   $$
--   \bigl(CW_q^{\otimes4}\bigr)_\sigma\ne0
--   \quad\Longleftrightarrow\quad
--   \exists\,r,t\in\{0,\ldots,14\},\quad g_r+g_t=\sigma.
--   $$
--   Addition is coordinatewise and the pair $(r,t)$ is ordered. Thus the two square-component indices represent exactly the supported coarse fourth-power grades. The statement concerns the actual canonical tensor blocks over $K$ and applies in particular to the DWZ parameter $q=5$.
--
--   **Formalization Note** Positivity of $q$ is witnessed by a chosen element of $\mathrm{Fin}(q)$. The square-grade coordinates are the already-public functions shapeX, shapeY, and shapeZ; no new grading or replacement tensor is introduced.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Section 5, printed p. 363: the 225 ordered square-block pairs are grouped by coordinate sums into 45 fourth-power shapes, https://www.maths.ed.ac.uk/~sandy/a11164.pdf. R. Duan, H. Wu, and R. Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Sections 6–7: higher-level components and their lower-level splits. This is an explicit source-indexing adapter for the existing canonical grading, not an additional component-value claim.

import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_stothers_fourth_data

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_dwz_fourth_canonical_support_square_pairs
    {K : Type u} [Field K] (q : ℕ) (i : Fin q)
    (sigma : Fin 3 → Fin 9) :
    (MME.StothersFourth.cwFourthCanonicalGrading K q).blockTensor sigma ≠ 0 ↔
      ∃ p : Fin 15 × Fin 15,
        (DWZSquare.shapeX p.1).val + (DWZSquare.shapeX p.2).val =
          (sigma 0).val ∧
        (DWZSquare.shapeY p.1).val + (DWZSquare.shapeY p.2).val =
          (sigma 1).val ∧
        (DWZSquare.shapeZ p.1).val + (DWZSquare.shapeZ p.2).val =
          (sigma 2).val := by
  sorry
