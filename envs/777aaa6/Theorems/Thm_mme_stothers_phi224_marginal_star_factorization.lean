-- Prove2me | Theorems.Thm_mme_stothers_phi224_marginal_star_factorization
-- name    : mme_stothers_phi224_marginal_star_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:34:24.631934+00:00
-- url     : https://prove2.me/theorems/4f858f4a-7bca-4ab9-83aa-a8c94a12a848
-- title:
--   Exact fixed-mode star factorization of the phi_224 ambient family
-- statement:
--   Fix a mode $i$ and any realized mode word $a_i$ in the full same-marginal $\varphi_{224}$ family $S$. Let
--
--   $$
--   W_i=\frac{(2N)!}{\prod_{s=0}^{4}m_{i,s}!}
--   $$
--
--   be the number of words with the prescribed mode-$i$ grade histogram. Then
--
--   $$
--   |S|=W_i\,|\{b\in S:b_i=a_i\}|.
--   $$
--
--   Thus the ambient completion hypergraph is exactly regular over every realized word in each mode. This factorization converts the global same-marginal/exact-profile completion ratio into a sharp local collision-degree ratio.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), equations (3.5)--(3.6) and the type-2 regularity/counting argument in Lemma 5.1(iv), pp. 359--360 and 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data
import Theorems.Thm_mme_stothers_phi224_profile_histogram_class_card
import Theorems.Thm_mme_stothers_phi224_fixed_mode_histogram_fiber_card

open BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

theorem mme_stothers_phi224_marginal_star_factorization
    (N alpha beta gamma delta : ℕ)
    (a : MME.StothersFourth.Phi224.MarginalProfileWord
      N alpha beta gamma delta) (i : Fin 3) :
    Nat.card
        (MME.StothersFourth.Phi224.MarginalProfileWord
          N alpha beta gamma delta) =
      ((2 * N).factorial /
        ∏ s : Fin 5,
          (MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s).factorial) *
        Nat.card
          {b : MME.StothersFourth.Phi224.MarginalProfileWord
              N alpha beta gamma delta //
            MME.StothersFourth.Phi224.modeWord b.1 i =
              MME.StothersFourth.Phi224.modeWord a.1 i} := by
  sorry
