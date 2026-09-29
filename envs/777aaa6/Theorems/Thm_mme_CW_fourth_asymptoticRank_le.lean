-- Prove2me | Theorems.Thm_mme_CW_fourth_asymptoticRank_le
-- name    : mme_CW_fourth_asymptoticRank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T15:56:29.064372+00:00
-- url     : https://prove2.me/theorems/0b7f6c02-f372-491a-8993-682eb3c4a7dd
-- title:
--   The fourth CW tensor has asymptotic rank at most (q+2)^4
-- statement:
--   Let $K$ be any field and let $q$ be a nonnegative integer. The literal fourth Coppersmith–Winograd tensor satisfies
--   $$
--   \widetilde R(CW_q^{\otimes4})\le(q+2)^4.
--   $$
--   In particular, at the DWZ fourth-power parameter $q=5$, its asymptotic-rank budget is at most $2401$.
--
--   **Formalization Note** The object is the already-public, parenthesized tensor $((CW_q\otimes CW_q)\otimes(CW_q\otimes CW_q))$. The claim is an upper bound, and does not assume any value, numerical witness, or exponent improvement.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Section 3.1, printed p. 16 (asymptotic rank), Section 3.4 (the CW tensor has asymptotic rank q+2), and Table 3, printed p. 78 (fourth-power analysis); https://arxiv.org/abs/2210.10173. This is the fourth-power consequence of the existing CW square rank bound and power multiplicativity.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_tensor_rank

open MME

universe u

set_option autoImplicit false

theorem mme_CW_fourth_asymptoticRank_le
    {K : Type u} [Field K] (q : ℕ) :
    tensorAsymptoticRank (MME.StothersFourth.cwFourthObj K q) ≤
      ((q : ℝ) + 2) ^ (4 : ℕ) := by
  sorry
