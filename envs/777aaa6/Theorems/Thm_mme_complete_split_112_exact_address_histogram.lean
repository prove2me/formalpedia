-- Prove2me | Theorems.Thm_mme_complete_split_112_exact_address_histogram
-- name    : mme_complete_split_112_exact_address_histogram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T21:45:12.085389+00:00
-- url     : https://prove2.me/theorems/768cd516-c330-46c7-84c0-bebf4339af24
-- title:
--   112 retained addresses have the full three-mode complete histogram
-- statement:
--   Let $N,L,G$ be natural numbers with $L+G=N$, and let $p$ be rational with $L=2Np$. Consider any supported coupled address at length $2N$ whose first two mode-grade histograms are $(N,N,0)$ and whose third is $(L,L,2G)$. Translating each internal grade to its actual complete two-letter fine word, every mode $i$ and fine word $\sigma$ satisfy
--
--   $$\#\{r\in[2N]:\mathrm{fineWord}(i,a_i(r))=\sigma\}=2N\,\beta_i(\sigma).$$
--
--   Here $\beta_X=\beta_Y$ is uniform on $01,10$, and $\beta_Z$ has masses $p,1-2p,p$ on $02,11,20$. The equality is denominator-free and includes length zero.
--
--   In particular, for the exact released first active $112$ consumer, put $N=1180591620717411303424m$, $L=8959763742786037m$, and $G=1180582660953668517387m$. For every natural $m$, the same identity holds over the reals for the published actual mode profiles, with no changes to the released rational parameter.
--
--   This is the all-three-mode counting bridge needed to land a retained-address tensor extraction inside the complete-profile projection. It does not assert existence of an induced address family, extraction maps, a tensor-value bound or numerical feasibility of the entire witness.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definitions3.4–3.6 (printed pp14–15); OSF https://osf.io/mw5ak/ code_matrix_mult.zip version1, src/evaluation/TermInfoLv2.m lines134–146, defining the 112 complete profiles. Exact released specialization: data/W1.00_2.371339.mat params(923), SHA256783353fda82acb3fb93c247dcad857b2db5f61944f5d0e91ae5f9e5a6c7feec3. Address marginals reuse the coupled four-block laser-method profile of Coppersmith–Winograd1990 journal p270, public CWQ6ExactCoupledAddress (its finite definition is independent of q). The fine-word translation agrees with public dwzCanonical112Pair: XY grades0,1 correspond to01,10; Z grades0,1,2 correspond to20,02,11. This is an exact finite histogram bridge, not a component-value assertion.

import Definitions.Def_mme_complete_split_112_address_words
import Definitions.Def_mme_more_asymmetry_first_112_profile_data
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 4096

open MME MME.CompleteSplit112 BigOperators

theorem mme_complete_split_112_exact_address_histogram :
    (∀ (N L G : ℕ) (p : ℚ), L + G = N →
      (L : ℚ) = (2 * N : ℕ) * p →
      ∀ (address : CWQ6ExactCoupledAddress N L G)
        (mode : Fin 3) (word : Fin 2 → Fin 3),
        (Fintype.card {r : Fin (2 * N) //
          fineWord mode (address.1 mode r) = word} : ℚ) =
          (2 * N : ℕ) * profileProbability p mode word) ∧
    (∀ (m : ℕ)
      (address : CWQ6ExactCoupledAddress
        (1180591620717411303424 * m)
        (8959763742786037 * m)
        (1180582660953668517387 * m))
      (mode : Fin 3) (word : Fin 2 → Fin 3),
      (Fintype.card {r : Fin (2 * (1180591620717411303424 * m)) //
        fineWord mode (address.1 mode r) = word} : ℝ) =
        (2 * (1180591620717411303424 * m) : ℕ) *
          (MoreAsymmetryFirstSlice.probability 0 mode word : ℝ)) := by sorry
