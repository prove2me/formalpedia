-- Prove2me | Theorems.Thm_mme_CW_fourth_boundary_literal_code_restrict
-- name    : mme_CW_fourth_boundary_literal_code_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:26:05.941586+00:00
-- url     : https://prove2.me/theorems/461cdf5c-2bc5-4782-9f62-8f25b555d95a
-- title:
--   A fixed-weight boundary code gives a fourth-power CW restriction
-- statement:
--   Let $C$ be a finite code whose codewords are four-letter words in the boundary alphabet of the Coppersmith--Winograd tensor: the $q$ middle summands have weight one, while the two endpoint summands have weights zero and two. Suppose the encoding $C\hookrightarrow(\{1,\ldots,q\}\sqcup\{B,C\})^4$ is injective and every codeword has total weight $j$. Then the grade-$(0,j,8-j)$ constituent of $CW_q^{\otimes4}$ restricts to the matrix-multiplication tensor $\langle1,1,|C|\rangle$: $$\langle1,1,|C|\rangle\leq_{\mathrm{res}}(CW_q^{\otimes4})_{0,j,8-j}.$$ This packages the literal-support argument behind the elementary rows of the Davie--Stothers fourth-power table into one reusable code theorem.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5, Lemma 5.1 and Table 1, p. 366; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_CW_boundary_literal_codes
import Definitions.Def_mme_tensor_bridge

open MME MME.StothersFourth

universe u

set_option autoImplicit false

theorem mme_CW_fourth_boundary_literal_code_restrict
    {K : Type u} [Field K] (q : ℕ)
    {C : Type u} [Fintype C] [DecidableEq C]
    (enc : C ↪ (Fin 4 → CWBoundaryLetter q))
    (j : Fin 9)
    (hweight : ∀ c, cwBoundaryWordWeight (enc c) = j.val) :
    TensorObj.Restrict (MMObj K 1 1 (Fintype.card C))
      (cwFourthConstituent K q 0 j ⟨8 - j.val, by omega⟩) := by
  sorry
