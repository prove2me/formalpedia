-- Prove2me | Theorems.Thm_mme_stothers_general_exact_outer_address_regular
-- name    : mme_stothers_general_exact_outer_address_regular
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T05:11:59.046964+00:00
-- url     : https://prove2.me/theorems/1bad8558-f658-4fc0-9095-d568676eff9a
-- title:
--   Exact-profile addresses are supported and marginally regular
-- statement:
--   **An address with the exact joint profile is automatically supported and marginally regular.**
--
--   Fix an integral ten-class profile $\beta$ and a scale $m$, and let $a$ be an outer address of
--   length $N = 3Dm$ whose joint histogram over the $9^3$ ordered grade triples is exactly the
--   prescribed one: each triple $\sigma$ occurs $\sum_r [\sigma \sim \text{rep}_r]\,\beta_r m$ times.
--   Then
--
--   - **support:** every position $k$ satisfies $\sigma_1 + \sigma_2 + \sigma_3 = 8$, the fourth-power
--     support condition; and
--   - **marginal regularity:** for every mode $s$ and grade $j$, the letter $j$ occurs exactly
--     $M_j(\beta)\,m$ times in the $s$-th mode word, where $M_j(\beta) = (Q\beta)_j$.
--
--   Neither conclusion is assumed: both follow from the joint histogram alone. Support holds because
--   the prescribed multiplicity of an unsupported triple is zero -- no permutation orbit of a Table-1
--   representative contains a triple whose coordinates do not sum to $8$. Regularity holds because
--   summing the joint histogram over the triples with $s$-th coordinate $j$ is, by Equation (5.2),
--   exactly $M_j(\beta) m$, and this is independent of the mode $s$.
--
--   This places every exact-profile address inside the marginal-supported ambient hypergraph on which
--   the outer hash operates, at any profile. It is the profile-parametric form of the published
--   fixed-witness statement.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5, Table 1 and Equation (5.2); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_general_exact_outer_address_regular
    (base : Fin 10 → ℕ) (m : ℕ)
    (a : MME.StothersFourth.GenExactOuterAddress base m) :
    MME.StothersFourth.GenCoordinatewiseSupported a.1 ∧
      MME.StothersFourth.GenMarginallyRegular a.1 := by
  sorry
