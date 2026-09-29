-- Prove2me | Theorems.Thm_mme_stothers_phi134_exact_profile_fine_factorization
-- name    : mme_stothers_phi134_exact_profile_fine_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:52:10.351885+00:00
-- url     : https://prove2.me/theorems/1ac345ab-0c41-434f-8b5f-22a8c557a00a
-- title:
--   Exact phi_134 component product restricts to its literal fine-coordinate product
-- statement:
--   Fix an exact $\Phi_{1,3,4}$ profile of length $2N$, with multiplicities $(\alpha,\beta,\gamma,\delta,\delta,\gamma,\beta,\alpha)$ on the eight fine types. The Kronecker product of the eight algebraic component payloads with those multiplicities restricts to the coordinatewise product of the literal fourth-power fine blocks selected by the profile address. This is the factorization step that connects the component value estimates to the literal graded constituent.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(iii), p. 365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_stothers_phi134_exact_label

open MME

universe u

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

theorem mme_stothers_phi134_exact_profile_fine_factorization
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (address : MME.StothersFourth.Phi134.ExactProfileAddress
      N alpha beta gamma delta) :
    TensorObj.Restrict
      (TensorObj.kronFin 8 (fun r ↦
        (MME.StothersFourth.Phi134.componentObj K q r).kronPow
          (MME.StothersFourth.Phi134.profileMultiplicity
            alpha beta gamma delta r)))
      (TensorObj.kronFin (2 * N) (fun j ↦
        MME.StothersFourth.Phi134.fineSourceObj K q
          (MME.StothersFourth.Phi134.exactLabelAt address j))) := by
  sorry
