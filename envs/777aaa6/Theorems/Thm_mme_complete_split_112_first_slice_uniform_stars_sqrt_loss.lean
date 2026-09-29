-- Prove2me | Theorems.Thm_mme_complete_split_112_first_slice_uniform_stars_sqrt_loss
-- name    : mme_complete_split_112_first_slice_uniform_stars_sqrt_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T22:29:43.720709+00:00
-- url     : https://prove2.me/theorems/9f57d479-7df8-4e58-ab51-ed258c0f87e2
-- title:
--   Uniform induced shared-Z families on the exact first active 112 profile subsequence
-- statement:
--   For the first active 112 consumer of the released More Asymmetry witness, write D=1180591620717411303424, l=8959763742786037 and g=1180582660953668517387. There is one constant C≥0 such that, for every sufficiently large integer m, the exact counts N=Dm, L=lm, G=gm admit an induced primary hash family of A>0 outer stars and H>0 components per star. Set Z=choose(2N,L)choose(2N−L,L), X=choose(N,G) and B=choose(2G,G). The family satisfies H≤4^N, Z exp(−C sqrt(N+1))≤A, and B exp(−C sqrt(N+1))≤4X²H. This preserves the separate outer-family and common-fiber count estimates. The exact profile scalar is p=l/(2D), so these are the same integer indices used by the proved actual-profile histogram and all-mode restricted extraction. The historical CWQ6 family type is independent of q. This theorem supplies finite combinatorial families along an exact cofinal subsequence; it does not claim a scalar tensor value, a limiting exponent, or full numerical witness feasibility.
-- source:
--   Exact-subsequence specialization of the proved theorem mme_CW_q6_primary_hash_uniform_stars_sqrt_loss (Prove2Me ff1bc517-79c4-4b19-80e0-7c8195bc94c4), whose source is Coppersmith and Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation9 (1990), journal pp.270–271, https://doi.org/10.1016/S0747-7171(08)80013-2. The exact selected scalar is params(923) in the pinned OSF mw5ak release, data/W1.00_2.371339.mat (SHA256 783353fda82acb3fb93c247dcad857b2db5f61944f5d0e91ae5f9e5a6c7feec3), evaluated by src/evaluation/TermInfoLv2.m lines134–146: https://osf.io/mw5ak/. Its profile semantics are More Asymmetry, arXiv:2404.16349v2, Definitions3.4–3.6, https://arxiv.org/abs/2404.16349v2. This is a finite formal adapter, not a separately stated numbered source theorem.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_mme_CW_q6_primary_hash_family

open MME Filter Topology

set_option autoImplicit false

theorem mme_complete_split_112_first_slice_uniform_stars_sqrt_loss :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let N : ℕ := 1180591620717411303424 * m
        let L : ℕ := 8959763742786037 * m
        let G : ℕ := 1180582660953668517387 * m
        let Zcount : ℕ := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
        let Xcount : ℕ := Nat.choose N G
        let middle : ℕ := Nat.choose (2 * G) G
        ∃ A H : ℕ,
          ∃ _family : CWQ6PrimaryHashFamily N L G A H,
            0 < A ∧ H ≤ 4 ^ N ∧
            (Zcount : ℝ) *
                Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
              (A : ℝ) ∧
            (middle : ℝ) *
                Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
              4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by sorry
