-- Prove2me | Theorems.Thm_mme_complete_split_112_parametric_profile_canonical_stars
-- name    : mme_complete_split_112_parametric_profile_canonical_stars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T00:12:27.119524+00:00
-- url     : https://prove2.me/theorems/3d7a544d-ee42-44c7-be6e-7af4d55f15e1
-- title:
--   Every rational112 complete profile admits literal same-family canonical star extraction
-- statement:
--   Let $p\in\mathbb Q$ satisfy $0\le p\le1/2$. There are normalized, nonnegative complete profiles $\beta_X,\beta_Y,\beta_Z$ with
--
--   $$\beta_X(01)=\beta_X(10)=\beta_Y(01)=\beta_Y(10)=1/2,$$
--   $$\beta_Z(02)=\beta_Z(20)=p,\qquad \beta_Z(11)=1-2p,$$
--
--   and all other probabilities zero. Their support is contained in the actual $112$ coarse grades; full support is not assumed at the endpoints.
--
--   The profiles can be chosen once so that the following holds for every field $K$, every integer $q\ge0$, and every actual induced family of exact coupled addresses with $L+G=N$ and $L=2Np$. At every nonnegative tolerance, the canonical $112$ block of $\mathrm{CW}_q^{\otimes2}$ raised to power $2N$ and simultaneously filtered by these three profiles restricts to the direct sum of the family's literal shared-third-mode stars. Those same stars have their prescribed $H$-component support, and every actual component is mutually restrictable with
--
--   $$\langle q^{2G},q^{2L},q^{2G}\rangle.$$
--
--   The result includes $p=0$, $p=1/2$, $N=0$, and $q=0$. It is a finite source-faithful structural theorem, conditional on an actual finite family, not on a tensor-value or exponent bound. No coherent whole-star matrix identification or ambient finrank equality is asserted.
-- source:
--   Finite formal adapter for the112 split profile in Duan, Wu and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section6.3 (printed pp58–59), https://arxiv.org/abs/2210.10173v5, and the simultaneous ordered complete-profile filter in Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definitions3.4–3.6 (printed pp14–15), https://arxiv.org/abs/2404.16349v2. This new packaging theorem proves the nine-word normalization and both endpoint cases directly, then reuses the existing exact extraction maps, all-mode profile descent, and canonical basis router. It is not claimed as a separately numbered theorem in either source.

import Definitions.Def_mme_complete_split_112_address_words
import Definitions.Def_mme_complete_split_112_canonical_source_data
import Definitions.Def_mme_complete_split_112_coupled_grading_data
import Definitions.Def_mme_coupled_Ctensor_packaging_data

open MME MME.CompleteSplit MME.CompleteSplit112
open CoupledCTensorPackaging
open scoped NNReal

universe u

set_option autoImplicit false

theorem mme_complete_split_112_parametric_profile_canonical_stars (p : ℚ) (hp : 0 ≤ p) (hp2 : 2 * p ≤ 1) :
    ∃ beta : Fin 3 → Profile 2,
      (∀ mode sigma, (beta mode).probability sigma =
        (profileProbability p mode sigma : ℝ)) ∧
      (∀ mode sigma,
        (sigma 0).val + (sigma 1).val ≠ (cwSquareBlockType 1 1 2 mode).val →
          (beta mode).probability sigma = 0) ∧
      ∀ (K : Type u) [Field K] (q N L G A H : ℕ)
        (family : CWQ6PrimaryHashFamily N L G A H)
        (_hLG : L + G = N) (_hLp : (L : ℚ) = (2 * N : ℕ) * p)
        (epsilon : ℝ≥0),
        TensorObj.Restrict
          (TensorObj.bigAdd (starObj (grading K q) family))
          (restrictedCanonicalPower K q beta epsilon (2 * N)) ∧
        ∀ a : Fin A,
          (∀ sigma : Fin 3 → Fin (H + 1),
            sigma ∉ Finset.univ.image (cTensorOneHOneAddress H) →
              (starGrading (grading K q) family a).blockTensor sigma = 0) ∧
          ∀ h : Fin H,
            TensorObj.Isomorphic
              (MMObj K (q ^ (2 * G)) (q ^ (2 * L)) (q ^ (2 * G)))
              ((starGrading (grading K q) family a).blockSubtensor
                (cTensorOneHOneAddress H h)) := by sorry
