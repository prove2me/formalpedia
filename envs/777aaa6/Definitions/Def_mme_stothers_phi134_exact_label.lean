-- Prove2me | Definitions.Def_mme_stothers_phi134_exact_label
-- name    : mme_stothers_phi134_exact_label
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-05T10:41:07.582328+00:00
-- url     : https://prove2.me/theorems/3e6a3db0-930c-4da3-b40a-585b5ea8f671
-- title:
--   Canonical fine-block label of an exact phi_134 address
-- statement:
--   For each coordinate of a supported exact $\Phi_{1,3,4}$ profile, select the corresponding one of the eight fine-block labels. The accompanying structural identity states that applying the eight-label pattern map recovers the coordinate's three first-square grades. This provides a stable index for grouping literal tensor factors by their exact profile multiplicities.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(iii), printed p. 365, and the eight-term decomposition used in its proof; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi134_profile_data

open MME

namespace MME.StothersFourth.Phi134

set_option autoImplicit false

noncomputable def exactLabelAt
    {N alpha beta gamma delta : ℕ}
    (x : ExactProfileAddress N alpha beta gamma delta)
    (j : Fin (2 * N)) : Fin 8 :=
  Classical.choose (x.1.2.1 j)

@[simp] theorem addressType_exactLabelAt
    {N alpha beta gamma delta : ℕ}
    (x : ExactProfileAddress N alpha beta gamma delta)
    (j : Fin (2 * N)) :
    addressType x.1.1 j = pattern (exactLabelAt x j) :=
  Classical.choose_spec (x.1.2.1 j)

end MME.StothersFourth.Phi134


