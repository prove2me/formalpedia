-- Prove2me | Definitions.Def_mme_stothers_phi233_marginal_profile_table
-- name    : mme_stothers_phi233_marginal_profile_table
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T23:33:09.368787+00:00
-- url     : https://prove2.me/theorems/0931375a-5215-4ac6-b845-a28fce960183
-- title:
--   Joint profile table of a same-marginal phi_233 address
-- statement:
--   Every coordinate of a same-marginal $\varphi_{233}$ address realizes exactly one of the ten supported fine-block patterns. The canonical label function records that pattern, and the profile table records the multiplicity of each of the ten labels. Unlike an exact target profile, a general same-marginal completion may have a different joint table while preserving all three five-grade marginals. This table is the finite index used to stratify fixed-mode completion fibers.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, the ten-term phi_233 profile and its same-marginal completion family in Lemma 5.1(v), pp. 365--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi233_profile_data

open MME

namespace MME.StothersFourth.Phi233

set_option autoImplicit false

/-- The unique ten-pattern label selected at one coordinate of a same-marginal phi_233 address. -/
noncomputable def marginalLabelAt
    {N alpha beta gamma delta : ℕ}
    (x : MarginalAddress N alpha beta gamma delta)
    (j : Fin (2 * N)) : Fin 10 :=
  Classical.choose (x.2.1 j)

@[simp] theorem addressType_marginalLabelAt
    {N alpha beta gamma delta : ℕ}
    (x : MarginalAddress N alpha beta gamma delta)
    (j : Fin (2 * N)) :
    addressType x.1 j = pattern (marginalLabelAt x j) :=
  Classical.choose_spec (x.2.1 j)

/-- The ten-entry joint profile table of a same-marginal address. -/
noncomputable def marginalProfileTable
    {N alpha beta gamma delta : ℕ}
    (x : MarginalAddress N alpha beta gamma delta) : Fin 10 → ℕ :=
  fun r ↦ Fintype.card {j : Fin (2 * N) // marginalLabelAt x j = r}

end MME.StothersFourth.Phi233


