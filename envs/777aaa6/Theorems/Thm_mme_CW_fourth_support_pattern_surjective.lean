-- Prove2me | Theorems.Thm_mme_CW_fourth_support_pattern_surjective
-- name    : mme_CW_fourth_support_pattern_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T19:33:20.762886+00:00
-- url     : https://prove2.me/theorems/29731107-647d-4e15-8cd6-1beae782b875
-- title:
--   Every total-degree-eight address is a fourfold CW support pattern
-- statement:
--   Every ordered triple $(i,j,k)$ with entries in $\{0,\ldots,8\}$ and $i+j+k=8$ is the coordinatewise sum of four patterns chosen from $(0,1,1),(1,0,1),(1,1,0),(0,0,2),(0,2,0),(2,0,0)$. Equivalently, every one of the 45 fourth-power outer addresses is realized by four monomials from the six-term support of a Coppersmith--Winograd tensor. This is the parameter-independent finite support interface used by both the Davie--Stothers and DWZ fourth-power analyses.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Royal Soc. Edinburgh 143A (2013), Section 5, printed p. 363, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_CW_fourth_support_patterns

open BigOperators

set_option autoImplicit false

theorem mme_CW_fourth_support_pattern_surjective
    (sigma : Fin 3 → Fin 9)
    (hsum : (∑ s, (sigma s).val) = 8) :
    ∃ r : Fin 4 → Fin 6,
      ∀ s, MME.StothersFourth.cwFourSupportNatAddress r s = (sigma s).val := by
  sorry
