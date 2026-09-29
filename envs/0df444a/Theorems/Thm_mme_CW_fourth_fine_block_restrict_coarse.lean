-- Prove2me | Theorems.Thm_mme_CW_fourth_fine_block_restrict_coarse
-- name    : mme_CW_fourth_fine_block_restrict_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:51:47.785167+00:00
-- url     : https://prove2.me/theorems/521ea33c-1983-47a3-a44a-8d25ef4d511c
-- title:
--   A product-grading block restricts from its summed fourth-power block
-- statement:
--   Write the fourth Coppersmith--Winograd power as the Kronecker product of two squares. Let $s_x$ and $s_y$ be ordered three-mode block types in the canonical five-gradings of the square, and let $\sigma$ be a block type in the canonical nine-grading of the fourth power. If $s_x(r)+s_y(r)=\sigma(r)$ in each tensor mode $r$, then the literal product-grading block indexed by $(s_x,s_y)$ is a tensor restriction of the coarse fourth-power block indexed by $\sigma$. This is the canonical fine-to-coarse projection bridge; it retains the actual graded subspaces and does not replace the coarse block by a formal external sum.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5, pp. 363--368; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. This theorem formalizes the canonical coarsening from ordered square-block pairs to their componentwise grade sums.

import Definitions.Def_mme_stothers_phi116_fine_blocks

open MME

universe u

set_option autoImplicit false

theorem mme_CW_fourth_fine_block_restrict_coarse
    {K : Type u} [Field K] (q : ℕ)
    (sx sy : Fin 3 → Fin 5) (sigma : Fin 3 → Fin 9)
    (hsum : ∀ s, (sx s).val + (sy s).val = (sigma s).val) :
    TensorObj.Restrict
      ((TensorObj.TypeGrading.kronGrading
        (cwSquareCanonicalGrading K q)
        (cwSquareCanonicalGrading K q)).blockSubtensor
          (fun s ↦ finProdFinEquiv (sx s, sy s)))
      ((MME.StothersFourth.cwFourthCanonicalGrading K q).blockSubtensor
        sigma) := by
  sorry
