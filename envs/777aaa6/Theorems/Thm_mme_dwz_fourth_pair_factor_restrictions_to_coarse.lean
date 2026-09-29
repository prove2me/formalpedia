-- Prove2me | Theorems.Thm_mme_dwz_fourth_pair_factor_restrictions_to_coarse
-- name    : mme_dwz_fourth_pair_factor_restrictions_to_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T15:20:51.723157+00:00
-- url     : https://prove2.me/theorems/2f0f942c-f98b-434a-bcdf-7038bace1b77
-- title:
--   Two square-component restrictions land in their actual fourth-power block
-- statement:
--   Let $K$ be any field, let $q$ be a nonnegative integer, and let $g_r,g_t\in\{0,\ldots,4\}^3$ be two of the fifteen square-grade labels in DWZ Table 2 order. Let $\sigma\in\{0,\ldots,8\}^3$ satisfy $g_r+g_t=\sigma$ coordinatewise. Suppose tensors $X$ and $Y$ are restrictions of the corresponding canonical square blocks. Then
--   $$
--   X\preceq\bigl(CW_q^{\otimes2}\bigr)_{g_r},
--   \qquad
--   Y\preceq\bigl(CW_q^{\otimes2}\bigr)_{g_t}
--   \quad\Longrightarrow\quad
--   X\otimes Y\preceq\bigl(CW_q^{\otimes4}\bigr)_\sigma,
--   $$
--   where $A\preceq B$ means that $A$ is a tensor restriction of $B$.
--
--   This places a lower-level pair of constituent constructions inside the literal coarse fourth-power component needed by the recursive DWZ analysis. It is uniform in $q$, including $q=5$, and imposes no numerical-value or split-distribution assumptions.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Section 5, printed p. 363: the 225 ordered square-block pairs are grouped by coordinate sums into 45 fourth-power shapes, https://www.maths.ed.ac.uk/~sandy/a11164.pdf. R. Duan, H. Wu, and R. Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Sections 6–7: higher-level components and their lower-level splits. This is an explicit source-indexing adapter for the existing canonical grading, not an additional component-value claim.

import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_stothers_fourth_data

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_dwz_fourth_pair_factor_restrictions_to_coarse
    {K : Type u} [Field K] (q : ℕ) (p : Fin 15 × Fin 15)
    (sigma : Fin 3 → Fin 9)
    (hx : (DWZSquare.shapeX p.1).val + (DWZSquare.shapeX p.2).val =
      (sigma 0).val)
    (hy : (DWZSquare.shapeY p.1).val + (DWZSquare.shapeY p.2).val =
      (sigma 1).val)
    (hz : (DWZSquare.shapeZ p.1).val + (DWZSquare.shapeZ p.2).val =
      (sigma 2).val)
    {X Y : TensorObj K 3}
    (hX : TensorObj.Restrict X
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType
          (DWZSquare.shapeX p.1) (DWZSquare.shapeY p.1) (DWZSquare.shapeZ p.1))))
    (hY : TensorObj.Restrict Y
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType
          (DWZSquare.shapeX p.2) (DWZSquare.shapeY p.2) (DWZSquare.shapeZ p.2)))) :
    TensorObj.Restrict (TensorObj.kron X Y)
      ((MME.StothersFourth.cwFourthCanonicalGrading K q).blockSubtensor sigma) := by
  sorry
