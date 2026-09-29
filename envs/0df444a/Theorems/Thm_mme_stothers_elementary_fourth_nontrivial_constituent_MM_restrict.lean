-- Prove2me | Theorems.Thm_mme_stothers_elementary_fourth_nontrivial_constituent_MM_restrict
-- name    : mme_stothers_elementary_fourth_nontrivial_constituent_MM_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:55:10.39934+00:00
-- url     : https://prove2.me/theorems/3ea0f9f9-e43e-41fd-bd0b-e2b3c9f64ee0
-- title:
--   The four nontrivial elementary fourth-power CW constituents
-- statement:
--   For the canonical nine-grading of $CW_q^{\otimes4}$, the four non-scalar elementary constituents with a zero first grade contain the matrix-multiplication tensors
--
--   $$\begin{aligned}
--   T_{017}&\succeq\langle1,1,4q\rangle,\\
--   T_{026}&\succeq\langle1,1,6q^2+4\rangle,\\
--   T_{035}&\succeq\langle1,1,4q(q^2+3)\rangle,\\
--   T_{044}&\succeq\langle1,1,q^4+12q^2+6\rangle.
--   \end{aligned}$$
--
--   These dimensions are the coefficients of degrees $1,2,3,4$ in $(1+qx+x^2)^4$. The common grade-zero mode is retained, while the compatible square-block pairs concatenate in the other two modes. The omitted scalar row $T_{008}$ follows directly from the proved fine-to-coarse projection bridge and the scalar $004$ square block.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5 and Table 1, first five rows, p. 366; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. A. J. Stothers, On the Complexity of Matrix Multiplication, PhD thesis, 2010, Section 4.2; https://era.ed.ac.uk/handle/1842/4734.

import Definitions.Def_mme_stothers_fourth_data

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_elementary_fourth_nontrivial_constituent_MM_restrict
    {K : Type u} [Field K] (q : ℕ) :
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
