-- Prove2me | Theorems.Thm_mme_stothers_phi224_exact_profile_nonempty
-- name    : mme_stothers_phi224_exact_profile_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:36:30.095042+00:00
-- url     : https://prove2.me/theorems/b1deef76-9617-4240-8f88-a1167e4308cf
-- title:
--   Integral phi_224 exact profiles exist
-- statement:
--   For nonnegative integers $\alpha,\beta,\gamma,\delta$ satisfying $\alpha+2\beta+\gamma+\delta=N$, there exists a length-$2N$ word in the nine fine $\varphi_{224}$ types with multiplicities
--
--   $$
--   (\alpha,\beta,\gamma,\beta,2\delta,\beta,\gamma,\beta,\alpha).
--   $$
--
--   This supplies an actual distinguished finite profile at every integral scale satisfying the source normalization, rather than only an asymptotic real frequency vector.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), the integral type-2 profiles used in Lemma 3.3 and Lemma 5.1(iv), pp. 359--360 and 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data
import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_nonempty

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi224_exact_profile_nonempty
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + 2 * beta + gamma + delta = N) :
    Nonempty
      (MME.StothersFourth.Phi224.ExactProfileWord
        N alpha beta gamma delta) := by
  sorry
