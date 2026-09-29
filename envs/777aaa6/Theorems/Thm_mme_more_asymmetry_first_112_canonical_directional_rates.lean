-- Prove2me | Theorems.Thm_mme_more_asymmetry_first_112_canonical_directional_rates
-- name    : mme_more_asymmetry_first_112_canonical_directional_rates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T23:58:53.179722+00:00
-- url     : https://prove2.me/theorems/7fd2fa07-4ab2-4c7b-811c-3c06adfe836a
-- title:
--   The actual canonical first112 family attains its directional entropy and matrix-size rates
-- statement:
--   Choose once the exact released complete profiles $\beta$ of the first active $112$ consumer. Put $D=1180591620717411303424$, $l=8959763742786037$, $g=1180582660953668517387$ and $p=l/(2D)$. For every $\delta>0$ and all sufficiently large $m$, with $N=Dm$, $L=lm$, $G=gm$, there is one actual induced family with $A>0$ outer stars and $H>0$ components per star, satisfying
--
--   $$H\le4^N,\qquad 2N\bigl(H_{\mathrm{nat}}(\beta_Z)-\delta\bigr)\le\log A,\qquad 2N(\log2-\delta)\le\log(AH).$$
--
--   Here $H_{\mathrm{nat}}$ is entropy of the actual complete-word distribution, in natural units. Its only nonzero masses are $p,p,1-2p$. The displayed component sizes have exact logarithmic rates
--
--   $$\frac{\log(5^{2G})}{2N}=(1-2p)\log5,\qquad \frac{\log(5^{2L})}{2N}=2p\log5.$$
--
--   For the same combinatorial family, over every field and at every nonnegative tolerance, the simultaneous complete-profile restriction of the canonical $112$ block of $\mathrm{CW}_5^{\otimes2}$, raised to power $2N$, restricts to the direct sum of its literal shared-third-mode stars. Each star has its actual prescribed support, and each actual component is mutually restrictable with $\langle5^{2G},5^{2L},5^{2G}\rangle$. The source also has a C-tensor-family certificate with the same $A,H$ and component volume $5^{4G+2L}$.
--
--   The profile is uniform in the error budget, length, field and tolerance; one family realizes both count bounds and the literal component statements. No per-consumer minimum is taken. This finishes the directional rate package for the selected exact profile, not the unequal-consumer assembly, global recursive extraction or numerical exponent surplus. No whole-star matrix identification or equality of ambient mode-space dimensions is asserted.
-- source:
--   Derived same-family rate assembly for Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definitions3.4–3.6 printed pp14–15, and the pinned OSF release https://osf.io/mw5ak/, src/evaluation/TermInfoLv2.m lines134–146 and Workspace.m lines211–222. Parameters from data/W1.00_2.371339.mat, params(923), SHA256783353fda82acb3fb93c247dcad857b2db5f61944f5d0e91ae5f9e5a6c7feec3. The full-word entropy identity, compatible-length limits and literal-star assembly are proved here from accepted finite extraction and zero-cell-safe counting results; the final global optimized inequality is not assumed.

import Definitions.Def_mme_more_asymmetry_first_112_profile_data
import Definitions.Def_mme_complete_split_112_canonical_source_data
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_modern_entropy_data
import Definitions.Def_mme_complete_split_112_coupled_grading_data
import Definitions.Def_mme_coupled_Ctensor_packaging_data

open MME MME.CompleteSplit MME.CompleteSplit112 Filter
open CoupledCTensorPackaging
open scoped NNReal

universe u

set_option autoImplicit false

theorem mme_more_asymmetry_first_112_canonical_directional_rates :
    ∃ beta : Fin 3 → Profile 2,
      (∀ mode sigma, (beta mode).probability sigma =
        (MoreAsymmetryFirstSlice.probability 0 mode sigma : ℝ)) ∧
      ∀ delta : ℝ, 0 < delta →
        ∀ᶠ m : ℕ in atTop,
          let N : ℕ := 1180591620717411303424 * m
          let L : ℕ := 8959763742786037 * m
          let G : ℕ := 1180582660953668517387 * m
          let p : ℝ := 8959763742786037 / 2361183241434822606848
          ∃ A H : ℕ, ∃ family : CWQ6PrimaryHashFamily N L G A H,
            0 < A ∧ H ≤ 4 ^ N ∧
            ((2 * N : ℕ) : ℝ) *
                (Real.log 2 * mme_modern_entropyBits (beta 2).probability - delta) ≤
              Real.log (A : ℝ) ∧
            ((2 * N : ℕ) : ℝ) * (Real.log 2 - delta) ≤
              Real.log ((A : ℝ) * (H : ℝ)) ∧
            Real.log ((5 ^ (2 * G) : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ) =
              (1 - 2 * p) * Real.log 5 ∧
            Real.log ((5 ^ (2 * L) : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ) =
              (2 * p) * Real.log 5 ∧
            ∀ (K : Type u) [Field K] (epsilon : ℝ≥0),
              Nonempty
                (CTensorOneHOneFamilyCertificate
                  (restrictedCanonicalPower K 5 beta epsilon (2 * N))
                  A H (5 ^ (4 * G + 2 * L))) ∧
              TensorObj.Restrict
                (TensorObj.bigAdd (starObj (grading K 5) family))
                (restrictedCanonicalPower K 5 beta epsilon (2 * N)) ∧
              ∀ a : Fin A,
                (∀ sigma : Fin 3 → Fin (H + 1),
                  sigma ∉ Finset.univ.image (cTensorOneHOneAddress H) →
                    (starGrading (grading K 5) family a).blockTensor sigma = 0) ∧
                ∀ h : Fin H,
                  TensorObj.Isomorphic
                    (MMObj K (5 ^ (2 * G)) (5 ^ (2 * L)) (5 ^ (2 * G)))
                    ((starGrading (grading K 5) family a).blockSubtensor
                      (cTensorOneHOneAddress H h)) := by sorry
