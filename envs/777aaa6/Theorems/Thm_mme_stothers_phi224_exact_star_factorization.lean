-- Prove2me | Theorems.Thm_mme_stothers_phi224_exact_star_factorization
-- name    : mme_stothers_phi224_exact_star_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:34:18.363173+00:00
-- url     : https://prove2.me/theorems/f88286d1-3fa6-4cb9-a1e9-a6fc888798d1
-- title:
--   Exact fixed-mode star factorization of the phi_224 target family
-- statement:
--   Let the integral parameters define a valid exact $\varphi_{224}$ profile, fix a mode $i$, and fix any exact-profile word $a$. With
--
--   $$
--   W_i=\frac{(2N)!}{\prod_{s=0}^{4}m_{i,s}!},
--   $$
--
--   the exact-profile family $S_0$ satisfies
--
--   $$
--   |S_0|=W_i\,|\{b\in S_0:b_i=a_i\}|.
--   $$
--
--   The exact target therefore has the same mode-word factor $W_i$ as the full ambient completion family. This common factor is what makes the global polynomial completion ratio transfer without loss to each local mode degree.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), equations (3.5)--(3.6) and the type-2 regularity/counting argument in Lemma 5.1(iv), pp. 359--360 and 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data
import Theorems.Thm_mme_stothers_phi224_exact_profile_card
import Theorems.Thm_mme_stothers_phi224_exact_profile_marginals
import Theorems.Thm_mme_stothers_phi224_fixed_mode_exact_profile_fiber_card

open BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem mme_stothers_phi224_exact_star_factorization
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + 2 * beta + gamma + delta = N)
    (a : MME.StothersFourth.Phi224.ExactProfileWord
      N alpha beta gamma delta) (i : Fin 3) :
    Nat.card
        (MME.StothersFourth.Phi224.ExactProfileWord
          N alpha beta gamma delta) =
      ((2 * N).factorial /
        ∏ s : Fin 5,
          (MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s).factorial) *
        Nat.card
          {b : MME.StothersFourth.Phi224.ExactProfileWord
              N alpha beta gamma delta //
            MME.StothersFourth.Phi224.modeWord b.1 i =
              MME.StothersFourth.Phi224.modeWord a.1 i} := by
  sorry
