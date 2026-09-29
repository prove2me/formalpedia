-- Prove2me | Theorems.Thm_mme_more_asymmetry_first_112_canonical_family_certificate
-- name    : mme_more_asymmetry_first_112_canonical_family_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T22:37:40.456865+00:00
-- url     : https://prove2.me/theorems/3df013ae-7144-404a-aa64-31fcb03b065b
-- title:
--   The exact released112 profile retains a genuine family in the canonical CW5 source
-- statement:
--   There exists one triple $\beta$ of normalized complete profiles, exactly equal to the released first active $112$ consumer, such that the following holds uniformly over every field, nonnegative tolerance and compatible finite length. Write
--
--   $$D=1180591620717411303424,\quad l=8959763742786037,\quad g=1180582660953668517387.$$
--
--   For every $m,A,H\in\mathbb N$ and induced coupled-address family with parameters $(N,L,G)=(Dm,lm,gm)$, the literal canonical $112$ block of $\mathrm{CW}_5^{\otimes2}$, powered $2Dm$ times and simultaneously restricted to $\beta_X,\beta_Y,\beta_Z$, admits an $A$-star C-tensor family with $H$ components per star and common component volume
--
--   $$5^{4gm+2lm}.$$
--
--   The same complete profiles are chosen before the field, power, family and tolerance. The source uses its actual canonical subset bases and both literal fine grades. The sole remaining combinatorial input is the finite induced family; no tensor restriction, value, arbitrary grading, or profile landing is assumed. This theorem does not assert family existence at every length, asymptotic rates, or full numerical witness feasibility.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definitions3.4–3.6 (printed pp14–15), instantiated at the first active112 profile in the pinned OSF https://osf.io/mw5ak/ release. Exact p=params(923)=8959763742786037/2361183241434822606848, member data/W1.00_2.371339.mat SHA256783353fda82acb3fb93c247dcad857b2db5f61944f5d0e91ae5f9e5a6c7feec3; profile formulas TermInfoLv2.m lines134–146. This is the finite canonical-source assembly of proved exact histograms, concrete coupled grading/MM blocks, actual map vanishing, and all-mode profile transport—not the paper's global recursive extraction theorem.

import Definitions.Def_mme_more_asymmetry_first_112_profile_data
import Definitions.Def_mme_complete_split_112_canonical_source_data
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_q6_primary_hash_family

open MME MME.CompleteSplit MME.CompleteSplit112
open scoped NNReal

universe u

set_option autoImplicit false

theorem mme_more_asymmetry_first_112_canonical_family_certificate :
    ∃ beta : Fin 3 → Profile 2,
      (∀ mode sigma, (beta mode).probability sigma =
        (MoreAsymmetryFirstSlice.probability 0 mode sigma : ℝ)) ∧
      ∀ (K : Type u) [Field K] (m A H : ℕ)
        (_family : CWQ6PrimaryHashFamily
          (1180591620717411303424 * m)
          (8959763742786037 * m)
          (1180582660953668517387 * m) A H)
        (epsilon : ℝ≥0),
        Nonempty
          (CTensorOneHOneFamilyCertificate
            (restrictedCanonicalPower K 5 beta epsilon
              (2 * (1180591620717411303424 * m)))
            A H (5 ^ (4 * (1180582660953668517387 * m) +
              2 * (8959763742786037 * m)))) := by sorry
