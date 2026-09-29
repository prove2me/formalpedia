-- Prove2me | Theorems.Thm_mme_stothers_elementary_fourth_constituent_MM_restrict
-- name    : mme_stothers_elementary_fourth_constituent_MM_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:42:49.284525+00:00
-- url     : https://prove2.me/theorems/e313ac18-4aa0-416a-b6c7-aaf690e9bf17
-- title:
--   The five elementary fourth-power CW constituents are matrix-multiplication tensors
-- statement:
--   For the canonical nine-grading of the fourth Coppersmith--Winograd power $T_q^{\otimes4}$, the five constituents whose first grade is zero contain the following rectangular matrix-multiplication tensors:
--
--   $$\begin{aligned}
--   T_{008}&\succeq\langle1,1,1\rangle,\\
--   T_{017}&\succeq\langle1,1,4q\rangle,\\
--   T_{026}&\succeq\langle1,1,6q^2+4\rangle,\\
--   T_{035}&\succeq\langle1,1,4q(q^2+3)\rangle,\\
--   T_{044}&\succeq\langle1,1,q^4+12q^2+6\rangle.
--   \end{aligned}$$
--
--   These are precisely the five explicitly decomposable rows of Davie--Stothers Table 1. Their dimensions are obtained by expanding the fourth-power block through the thirteen elementary blocks of the canonical CW square grading; no recursive laser extraction is involved.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5 and Table 1, first five rows, printed p. 366; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. A. J. Stothers, On the Complexity of Matrix Multiplication, PhD thesis, 2010, Section 4.2; https://era.ed.ac.uk/handle/1842/4734.

import Definitions.Def_mme_stothers_fourth_data

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_elementary_fourth_constituent_MM_restrict
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 1 1)
        (MME.StothersFourth.cwFourthConstituent K q 0 0 8) ∧
    TensorObj.Restrict (MMObj K 1 1 (4 * q))
        (MME.StothersFourth.cwFourthConstituent K q 0 1 7) ∧
    TensorObj.Restrict (MMObj K 1 1 (6 * q ^ 2 + 4))
        (MME.StothersFourth.cwFourthConstituent K q 0 2 6) ∧
    TensorObj.Restrict (MMObj K 1 1 (4 * q * (q ^ 2 + 3)))
        (MME.StothersFourth.cwFourthConstituent K q 0 3 5) ∧
    TensorObj.Restrict (MMObj K 1 1
        (q ^ 4 + 12 * q ^ 2 + 6))
      (MME.StothersFourth.cwFourthConstituent K q 0 4 4) := by
  sorry
