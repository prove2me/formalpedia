-- Prove2me | Theorems.Thm_mme_complete_split_112_disallowed_word_mismatches_exact_address
-- name    : mme_complete_split_112_disallowed_word_mismatches_exact_address
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T22:17:34.812065+00:00
-- url     : https://prove2.me/theorems/aa4d5e90-c128-4840-b341-9c19e8e66c18
-- title:
--   112 complete-profile rejection forces an exact-address mismatch
-- statement:
--   Fix a mode of the coupled $(1,1,2)$ constituent, a rational split parameter $p$, and compatible counts $L+G=N$, $L=2Np$. Let $\beta$ be the complete-word probability profile with masses $1/2,1/2$ on $01,10$ in the first two modes and $p,1-2p,p$ on $02,11,20$ in the third mode. Let an arbitrary coordinate alphabet carry the appropriate internal grade map. If a length-$2N$ coordinate word fails the complete-profile consistency test at nonnegative tolerance $\epsilon$, then it cannot match any exact retained address throughout that mode:
--
--   $$\neg\operatorname{ApproxConsistent}_{\beta,\epsilon}(w)\quad\Longrightarrow\quad\forall a\in\operatorname{ExactAddress}(N,L,G),\;\exists r\in[2N],\;\operatorname{grade}(w_r)\ne a_r.$$
--
--   The theorem also provides the direct actual-coordinate version for the released first active $112$ consumer: $N=1180591620717411303424m$, $L=8959763742786037m$, $G=1180582660953668517387m$. It uses the actual lifted coupled coordinate types, the actual internal grade map for arbitrary $q$, and the published released complete profiles. All three modes, every natural $m$ including zero, and every nonnegative tolerance are covered.
--
--   This is the finite mismatch condition consumed by basis-projection zeroing and extraction-map descent. It does not itself claim a tensor restriction, an induced address family, a component-value bound or full numerical feasibility.
-- source:
--   A direct finite consequence of complete-profile consistency in Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definitions3.4–3.6, printed pp14–15. The112 fine-word profile is the pinned OSF release https://osf.io/mw5ak/, code_matrix_mult.zip v1, src/evaluation/TermInfoLv2.m lines134–146; actual scalar is data/W1.00_2.371339.mat params(923), member SHA256783353fda82acb3fb93c247dcad857b2db5f61944f5d0e91ae5f9e5a6c7feec3. Exact retained-address histograms are imported from Proved mme_complete_split_112_exact_address_histogram, ID768cd516-c330-46c7-84c0-bebf4339af24. The mismatch-to-projected-word-zero strategy reuses the prior CW/DWZ formalization, while this statement specifically tests all three complete profiles.

import Definitions.Def_mme_complete_split_112_coupled_grading_data
import Theorems.Thm_mme_complete_split_112_exact_address_histogram
import Mathlib.Tactic

set_option autoImplicit false

open MME MME.CompleteSplit MME.CompleteSplit112 MME.DWZComponentRestriction
open scoped NNReal

universe u v

theorem mme_complete_split_112_disallowed_word_mismatches_exact_address :
    (∀ {ι : Type u} (N L G : ℕ) (p : ℚ),
      L + G = N → (L : ℚ) = (2 * N : ℕ) * p →
      ∀ (mode : Fin 3) (grade : ι → Fin 3) (beta : Profile 2),
        (∀ sigma, beta.probability sigma = (profileProbability p mode sigma : ℝ)) →
        ∀ (epsilon : ℝ≥0) (w : PowIndex ι (2 * N)),
          ¬ ApproxConsistent (fineWord mode ∘ grade) beta epsilon w →
          ∀ address : CWQ6ExactCoupledAddress N L G,
            ∃ r : Fin (2 * N),
              grade (PowIndex.get (2 * N) w r) ≠ address.1 mode r) ∧
    (∀ (q m : ℕ) (mode : Fin 3) (beta : Profile 2),
      (∀ sigma, beta.probability sigma =
        (MoreAsymmetryFirstSlice.probability 0 mode sigma : ℝ)) →
      ∀ (epsilon : ℝ≥0)
        (w : PowIndex (LiftedCoord.{u} q mode)
          (2 * (1180591620717411303424 * m))),
        ¬ ApproxConsistent (fineWord mode ∘ liftedCoordGrade q mode) beta epsilon w →
        ∀ address : CWQ6ExactCoupledAddress
          (1180591620717411303424 * m)
          (8959763742786037 * m)
          (1180582660953668517387 * m),
          ∃ r : Fin (2 * (1180591620717411303424 * m)),
            liftedCoordGrade q mode
                (PowIndex.get (2 * (1180591620717411303424 * m)) w r) ≠
              address.1 mode r) := by sorry
