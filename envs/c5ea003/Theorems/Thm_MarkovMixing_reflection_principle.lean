-- Prove2me | Theorems.Thm_MarkovMixing_reflection_principle
-- name    : MarkovMixing.reflection_principle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T01:44:04.390305+00:00
-- url     : https://prove2.me/theorems/023aa7f3-c11c-4b8e-8a78-d0675ccb0eef
-- title:
--   Lemma 2.18 -- the reflection principle on $\mathbb{Z}$
-- statement:
--   For simple random walk on $\mathbb{Z}$ started at $k>0$ and any $j>0$: walks of length $r$ that touch $0$ before time $r$ and end at $j$ are equinumerous with walks ending at $-j$, and walks that touch $0$ and end positive are equinumerous with walks ending negative. Stated as exact equalities of counts of $\pm1$ step sequences, which is equivalent to the probabilistic statement since all $2^r$ sequences are equally likely.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 2.7, Lemma 2.18 (Eqs. (2.20)-(2.21)), pp. 30-31

import Definitions.Def_mm_classical

namespace MarkovMixing

/-- **Lemma 2.18** (LPW), the reflection principle for simple random walk on
`ℤ`: for positive `j, k` and horizon `r`, walks from `k` that touch `0` before
time `r` and end at `j` are equinumerous with walks from `k` ending at `-j`;
consequently walks touching `0` and ending positive are equinumerous with
walks ending negative.  (All `2^r` sign sequences being equally likely, these
counting identities are exactly (2.20) and (2.21).) -/
theorem reflection_principle (r : ℕ) (k j : ℤ) (hk : 0 < k) (hj : 0 < j) :
    ((Finset.univ.filter fun ω : Fin r → Bool =>
        (∃ s < r, srwPos k ω s = 0) ∧ srwPos k ω r = j).card =
      (Finset.univ.filter fun ω : Fin r → Bool => srwPos k ω r = -j).card) ∧
    ((Finset.univ.filter fun ω : Fin r → Bool =>
        (∃ s < r, srwPos k ω s = 0) ∧ 0 < srwPos k ω r).card =
      (Finset.univ.filter fun ω : Fin r → Bool => srwPos k ω r < 0).card) := by
  sorry

end MarkovMixing
