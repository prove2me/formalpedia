-- Prove2me | Theorems.Thm_mme_CW_canonical_four_literal_address_eq_support_pattern
-- name    : mme_CW_canonical_four_literal_address_eq_support_pattern
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T19:37:40.265217+00:00
-- url     : https://prove2.me/theorems/24eca5fe-46de-4596-80e3-6fb965f8217f
-- title:
--   Canonical literal fourth addresses realize the six-pattern model
-- statement:
--   Fix $q>0$ through a middle coordinate of $CW_q$. For any four choices among the six canonical CW support types, the grade in each tensor mode of the corresponding literal fourth-power basis word equals the coordinatewise sum of the four abstract support patterns. Thus the finite six-pattern model is not merely combinatorial: it is realized by actual monomials of the literal tensor $CW_q^{\otimes 4}$. The statement is uniform in $q$, so it applies to both the $q=6$ Davie--Stothers source and the $q=5$ DWZ source.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Royal Soc. Edinburgh 143A (2013), Section 5, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173.

import Definitions.Def_mme_CW_fourth_support_patterns
import Definitions.Def_mme_CW_fourth_literal_support_words

set_option autoImplicit false

theorem mme_CW_canonical_four_literal_address_eq_support_pattern
    (q : ℕ) (i : Fin q) (r : Fin 4 → Fin 6) (s : Fin 3) :
    (MME.StothersFourth.cwCanonicalFourLiteralAddress q i r s).val =
      MME.StothersFourth.cwFourSupportNatAddress r s := by
  sorry
