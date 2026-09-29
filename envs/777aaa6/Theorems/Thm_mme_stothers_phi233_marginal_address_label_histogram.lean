-- Prove2me | Theorems.Thm_mme_stothers_phi233_marginal_address_label_histogram
-- name    : mme_stothers_phi233_marginal_address_label_histogram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:19:16.153223+00:00
-- url     : https://prove2.me/theorems/03e81b94-03fc-460e-8f90-6c5835e9c8cb
-- title:
--   Extract the ten-label histogram of a phi_233 marginal address
-- statement:
--   Every marginally regular $\varphi_{233}$ address of length $2N$ admits a label word $g$ in the ten ordered fine types that reproduces all three grade coordinates. If $w_r$ counts positions carrying label $r$, then $\sum_r w_r=2N$, the two outer first-mode sums $w_0+w_1+w_2$ and $w_7+w_8+w_9$ both equal $2\alpha+\beta$, and the four selected second- and third-mode sums $w_3+w_7$, $w_2+w_6$, $w_6+w_9$, and $w_0+w_3$ all equal $\alpha+\gamma$. This extracts from the literal address definition precisely the finite histogram equations needed by the exceptional entropy argument.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), exceptional type-2 profile construction around Equation (3.6), pp. 359--360, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Definitions.Def_mme_CW_square_five_grade_certificate

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000

theorem mme_stothers_phi233_marginal_address_label_histogram
    (N alpha beta gamma delta : ℕ)
    (x : MME.StothersFourth.Phi233.MarginalAddress
      N alpha beta gamma delta) :
    ∃ g : Fin (2 * N) → Fin 10,
      (∀ i j,
        x.1 i j = MME.StothersFourth.Phi233.pattern (g j) i) ∧
      let w : Fin 10 → ℕ := fun r ↦
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ g j = r)).card
      (∑ r : Fin 10, w r) = 2 * N ∧
      w 0 + w 1 + w 2 = 2 * alpha + beta ∧
      w 7 + w 8 + w 9 = 2 * alpha + beta ∧
      w 3 + w 7 = alpha + gamma ∧
      w 2 + w 6 = alpha + gamma ∧
      w 6 + w 9 = alpha + gamma ∧
      w 0 + w 3 = alpha + gamma := by
  sorry
