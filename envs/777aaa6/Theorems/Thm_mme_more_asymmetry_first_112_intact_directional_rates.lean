-- Prove2me | Theorems.Thm_mme_more_asymmetry_first_112_intact_directional_rates
-- name    : mme_more_asymmetry_first_112_intact_directional_rates
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T11:02:26.006058+00:00
-- url     : https://prove2.me/theorems/ec86ffc3-7f22-418e-b399-268344e86af3
-- title:
--   First-slice directional entropy rates in literal intact CW blocks
-- statement:
--   Put
--   $$C=1180591620717411303424,\quad L_0=8959763742786037,\quad G_0=1180582660953668517387,$$
--   so that $C=L_0+G_0$, and let $p=L_0/(2C)$. At scale $m$, set $N=Cm$, $L=L_0m$, and $G=G_0m$.
--
--   There exist integer complete-word histograms $\mu_m$ and profiles $\beta_i$ realizing the first-slice rational distributions exactly: $\mu_{m,i}(\sigma)=2N\beta_i(\sigma)$. In modes $X,Y$, the words $01,10$ each have count $N$. In mode $Z$, the words $02,20$ each have count $L$, and $11$ has count $2G$. All other counts vanish.
--
--   For every $\delta>0$, at all sufficiently large integer scales $m$, there are integers $A,H$ and a primary hash family such that $A>0$, $H\le4^N$, and
--   $$\log A\ge 2N\bigl((\log2)\,\mathcal H_2(\beta_Z)-\delta\bigr),\qquad
--   \log(AH)\ge2N(\log2-\delta),$$
--   where $\mathcal H_2$ is Shannon entropy in bits.
--
--   Over every field $K$, the literal intact block of $\mathrm{CW}_5^{\otimes4N}$, with $2N$ pairs of grade $(1,1,2)$ and histograms $\mu_m$, restricts to the direct sum of the family's $A$ directional star tensors. Each star is zero outside the designated $C_{1,H,1}$ support, and each of its $H$ designated blocks is isomorphic to
--   $$\langle5^{2G},5^{2L},5^{2G}\rangle.$$
--   The intact source also admits a $C_{1,H,1}$ family certificate of multiplicity $A$ and block volume $5^{4G+2L}$. The normalized logarithms of the long and short dimensions are respectively $(1-2p)\log5$ and $2p\log5$.
--
--   This is a first-slice extraction and rate statement for the literal intact block. It does not assert the global cofinal construction or its repair budgets.
-- source:
--   Consequence of the accepted first_112 canonical directional rates and exact canonical-power-to-intact-block restriction, with the released first-slice rational profile.

import Definitions.Def_mme_more_asymmetry_first_112_profile_data
import Definitions.Def_mme_complete_split_112_canonical_source_data
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_modern_entropy_data
import Definitions.Def_mme_complete_split_112_coupled_grading_data
import Definitions.Def_mme_coupled_Ctensor_packaging_data

import Theorems.Thm_mme_complete_split_112_canonical_power_restricts_from_intact
import Theorems.Thm_mme_more_asymmetry_first_112_canonical_directional_rates

open MME MME.CompleteSplit MME.CompleteSplit112 Filter
open CoupledCTensorPackaging
open scoped NNReal

universe u

set_option autoImplicit false

theorem mme_more_asymmetry_first_112_intact_directional_rates :
    ∃ mu : ℕ → Fin 3 → CompleteWord 2 → ℕ,
      (∀ m mode sigma, (mu m mode sigma : ℝ) =
        ((2 * (1180591620717411303424 * m) : ℕ) : ℝ) *
          (MoreAsymmetryFirstSlice.probability 0 mode sigma : ℝ)) ∧
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
            ∀ (K : Type u) [Field K],
              Nonempty
                (CTensorOneHOneFamilyCertificate
                  (MME.RecursiveYZ.CWCells.unbroken K 5 2 (2 * N)
                    (Equiv.refl _) (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
                    (fun i _ => mu m i))
                  A H (5 ^ (4 * G + 2 * L))) ∧
              TensorObj.Restrict
                (TensorObj.bigAdd (starObj (grading K 5) family))
                (MME.RecursiveYZ.CWCells.unbroken K 5 2 (2 * N)
                    (Equiv.refl _) (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
                    (fun i _ => mu m i)) ∧
              ∀ a : Fin A,
                (∀ sigma : Fin 3 → Fin (H + 1),
                  sigma ∉ Finset.univ.image (cTensorOneHOneAddress H) →
                    (starGrading (grading K 5) family a).blockTensor sigma = 0) ∧
                ∀ h : Fin H,
                  TensorObj.Isomorphic
                    (MMObj K (5 ^ (2 * G)) (5 ^ (2 * L)) (5 ^ (2 * G)))
                    ((starGrading (grading K 5) family a).blockSubtensor
                      (cTensorOneHOneAddress H h)) := by sorry
