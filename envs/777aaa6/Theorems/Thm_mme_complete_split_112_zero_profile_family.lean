-- Prove2me | Theorems.Thm_mme_complete_split_112_zero_profile_family
-- name    : mme_complete_split_112_zero_profile_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T00:08:38.273606+00:00
-- url     : https://prove2.me/theorems/c6a75b03-2f1e-4452-8ded-4a4f0c9b821d
-- title:
--   The zero112 profile has an explicit full balanced central-binomial star
-- statement:
--   For every natural number $N$, including $N=0$, there exists an exact primary coupled-address family with
--
--   $$L=0,\qquad G=N,\qquad A=1,\qquad H=\binom{2N}{N}\le4^N.$$
--
--   This is one outer star with $H$ components. Its first two grade words are exactly balanced and are globally distinct; its third grade word is constantly2 and is shared by the whole star. The family satisfies the full induced mixed-support condition.
--
--   The construction supplies the $p=0$ endpoint excluded by the positive-$L$ asymptotic hashing theorem. It assumes no tensor-value lower bound. The historical CWQ6 name of the family structure does not impose a tensor parameter: the address construction is purely combinatorial and independent of $q$.
-- source:
--   Explicit endpoint construction for the complete112 split profiles in Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definitions3.4–3.6 (printed pp14–15), and pinned OSF release https://osf.io/mw5ak/ src/evaluation/TermInfoLv2.m lines134–146. At p=0, X/Y use01 and10 equally, while Z uses11 only. Constructing the existing four-support primary family by all balanced binary words proves the endpoint exactly. This finite construction is an implementation lemma, not claimed to be a separately numbered theorem from the paper. The source audit finds228 active p=0 consumers across112/121/211 in data/W1.00_2.371339.mat; that activity audit is provenance, not a premise or a proof of global exact witness feasibility.

import Definitions.Def_mme_CW_q6_primary_hash_family

set_option autoImplicit false

theorem mme_complete_split_112_zero_profile_family (N : ℕ) :
    Nonempty (MME.CWQ6PrimaryHashFamily N 0 N 1 (Nat.choose (2 * N) N)) ∧
      Nat.choose (2 * N) N ≤ 4 ^ N := by sorry
