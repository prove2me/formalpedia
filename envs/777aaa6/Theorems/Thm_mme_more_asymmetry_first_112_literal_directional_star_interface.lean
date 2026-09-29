-- Prove2me | Theorems.Thm_mme_more_asymmetry_first_112_literal_directional_star_interface
-- name    : mme_more_asymmetry_first_112_literal_directional_star_interface
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T23:43:51.803251+00:00
-- url     : https://prove2.me/theorems/bef2f108-b5d2-471e-b72e-c0f830b81132
-- title:
--   The exact first112 profile retains its literal shared-Z stars with all three component dimensions
-- statement:
--   Choose the three normalized complete profiles of the first active $112$ consumer in the released More Asymmetry witness. Write
--
--   $$D=1180591620717411303424,\qquad l=8959763742786037,\qquad g=1180582660953668517387.$$
--
--   The profiles can be chosen once so that the following holds over every field, at every nonnegative profile tolerance, for every $m,A,H\in\mathbb N$ and every actual induced family with $(N,L,G)=(Dm,lm,gm)$.
--
--   The simultaneously profile-filtered canonical $112$ component of $\mathrm{CW}_5^{\otimes2}$, raised to power $2N$, restricts to the direct sum of the literal $A$ shared-third-mode stars constructed from that same induced family. In each star, the actual grading is supported only on its $H$ addresses of the form $(h,h,*)$, and each corresponding component is mutually restrictable with
--
--   $$\langle 5^{2G},\;5^{2L},\;5^{2G}\rangle.$$
--
--   This retains the actual shared-third-mode object and the separate matrix dimensions, not merely a freely chosen family with the same component volume. It supplies a structural interface for later directional aggregation without taking a per-consumer scalar minimum.
--
--   **Formalization Note.** The platform's `TensorObj.Isomorphic` means mutual tensor restriction. This statement does not assert a coherent matrix-multiplication identification of an entire star, ambient mode-space dimension equalities, asymptotic rates, family existence at every length, or full numerical-witness feasibility.
-- source:
--   Finite structural refinement of the enhanced112 construction in Duan, Wu and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section6.3, printed pp58–59, https://arxiv.org/abs/2210.10173; and the simultaneous complete-profile restriction in Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definitions3.4–3.6, printed pp14–15, https://arxiv.org/abs/2404.16349v2. Exact active profile from pinned OSF https://osf.io/mw5ak/ release: params(923)=8959763742786037/2361183241434822606848; TermInfoLv2.m lines134–146; data/W1.00_2.371339.mat SHA256783353fda82acb3fb93c247dcad857b2db5f61944f5d0e91ae5f9e5a6c7feec3. This is an explicitly derived finite adapter preserving the existing shared-Z star objects and component dimensions, not a separately numbered source theorem or the global recursive extraction.

import Definitions.Def_mme_more_asymmetry_first_112_profile_data
import Definitions.Def_mme_complete_split_112_canonical_source_data
import Definitions.Def_mme_complete_split_112_coupled_grading_data
import Definitions.Def_mme_coupled_Ctensor_packaging_data

open MME MME.CompleteSplit MME.CompleteSplit112
open CoupledCTensorPackaging
open scoped NNReal

universe u

set_option autoImplicit false

theorem mme_more_asymmetry_first_112_literal_directional_star_interface :
    ∃ beta : Fin 3 → Profile 2,
      (∀ mode sigma, (beta mode).probability sigma =
        (MoreAsymmetryFirstSlice.probability 0 mode sigma : ℝ)) ∧
      ∀ (K : Type u) [Field K] (m A H : ℕ)
        (family : CWQ6PrimaryHashFamily
          (1180591620717411303424 * m)
          (8959763742786037 * m)
          (1180582660953668517387 * m) A H)
        (epsilon : ℝ≥0),
        TensorObj.Restrict
          (TensorObj.bigAdd (starObj (grading K 5) family))
          (restrictedCanonicalPower K 5 beta epsilon
            (2 * (1180591620717411303424 * m))) ∧
        ∀ a : Fin A,
          (∀ sigma : Fin 3 → Fin (H + 1),
            sigma ∉ Finset.univ.image (cTensorOneHOneAddress H) →
              (starGrading (grading K 5) family a).blockTensor sigma = 0) ∧
          ∀ h : Fin H,
            TensorObj.Isomorphic
              (MMObj K (5 ^ (2 * (1180582660953668517387 * m)))
                (5 ^ (2 * (8959763742786037 * m)))
                (5 ^ (2 * (1180582660953668517387 * m))))
              ((starGrading (grading K 5) family a).blockSubtensor
                (cTensorOneHOneAddress H h)) := by sorry
