-- Prove2me | Theorems.Thm_mme_more_asymmetry_first_112_intact_square_extractions
-- name    : mme_more_asymmetry_first_112_intact_square_extractions
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T11:08:18.790457+00:00
-- url     : https://prove2.me/theorems/95910f07-3a59-48a3-ac37-9d6105e86fa5
-- title:
--   Square matrix extractions and entropy bounds for intact first-slice blocks
-- statement:
--   Let $C=1180591620717411303424$, $L_0=8959763742786037$, $G_0=1180582660953668517387$, and $p=L_0/(2C)$. Write $N=Cm$, $L=L_0m$, $G=G_0m$. There exist exact integer histograms $\mu_m=2N\beta$ for the first-slice profiles: the two $X,Y$ words $01,10$ have count $N$ each, while the $Z$ words $02,20,11$ have counts $L,L,2G$.
--
--   For every $\delta>0$, at all sufficiently large integer scales, there are positive $A$ and a primary hash family of $A$ stars with $H\le4^N$ leaves per star. They obey
--   $$\log A\ge2N((\log2)\mathcal H_2(\beta_Z)-\delta),\qquad
--   \log(AH)\ge2N(\log2-\delta),$$
--   where $\mathcal H_2$ is entropy in bits. The normalized long and short matrix-side logarithms are $(1-2p)\log5$ and $2p\log5$.
--
--   Let $U_m$ be the literal intact block of $\mathrm{CW}_5^{\otimes4N}$ with $2N$ pairs of grade $(1,1,2)$ and histograms $\mu_m$. Over every field $K$, the cyclic symmetrization of $U_m$ restricts to $k$ copies of the square matrix tensor $\langle d,d,d\rangle$, where $d=5^{4G+2L}$ and
--   $$k\ge A^3H^2\exp\!\bigl(-100\sqrt{\log(H+1)}\bigr).$$
--   In particular,
--   $$\log k\ge2N\bigl((\log2)(\mathcal H_2(\beta_Z)+2)-3\delta\bigr)
--   -100\sqrt{\log(H+1)}.$$
--   This gives actual square matrix extractions from the cyclically symmetrized intact source, with the complete outer-family count and an explicit loss. It does not assert a global cofinal stage construction or repair budgets.
-- source:
--   Consequence of the accepted first-slice intact directional rates and uniform outer-family three-star square extraction.

import Theorems.Thm_mme_more_asymmetry_first_112_intact_directional_rates
import Theorems.Thm_mme_Ctensor_uniform_outer_family_square_extraction

open MME MME.CompleteSplit MME.CompleteSplit112 Filter
open CoupledCTensorPackaging
open scoped NNReal
universe u
set_option autoImplicit false

theorem mme_more_asymmetry_first_112_intact_square_extractions :
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
          ∃ A H : ℕ, ∃ _family : CWQ6PrimaryHashFamily N L G A H,
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
            ∀ (K : Type u) [Field K], ∃ k : ℕ,
              TensorObj.Restrict
                (TensorObj.bigAdd (fun _ : Fin k =>
                  MMObj K (5 ^ (4 * G + 2 * L)) (5 ^ (4 * G + 2 * L))
                    (5 ^ (4 * G + 2 * L))))
                (cyclicSymmetrization
                  (MME.RecursiveYZ.CWCells.unbroken K 5 2 (2 * N)
                    (Equiv.refl _) (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
                    (fun i _ => mu m i))) ∧
              (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
                Real.exp (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))))) ≤
                (k : ℝ) ∧
              ((2 * N : ℕ) : ℝ) *
                  (Real.log 2 * (mme_modern_entropyBits (beta 2).probability + 2) -
                    3 * delta) -
                100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))) ≤ Real.log (k : ℝ) := by sorry
