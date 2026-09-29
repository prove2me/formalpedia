-- Prove2me | Theorems.Thm_mme_more_asymmetry_first_112_intact_square_entropy_rate
-- name    : mme_more_asymmetry_first_112_intact_square_entropy_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T11:11:31.381622+00:00
-- url     : https://prove2.me/theorems/08730ede-87e6-451b-b6ca-dc873c94b5e1
-- title:
--   Asymptotic square-matrix entropy rate for intact first-slice blocks
-- statement:
--   Put $C=1180591620717411303424$, $L_0=8959763742786037$, $G_0=1180582660953668517387$. At integer scale $m$, let $N=Cm$, $L=L_0m$, and $G=G_0m$.
--   There exist integer histograms $\mu_m$ and first-slice profiles $\beta$ satisfying $\mu_{m,i}(\sigma)=2N\beta_i(\sigma)$. The $X,Y$ words $01,10$ each have count $N$, and the $Z$ words $02,20,11$ have counts $L,L,2G$; all other counts are zero.
--
--   Let $U_m$ be the literal intact block of $\mathrm{CW}_5^{\otimes4N}$ with $2N$ pairs of grade $(1,1,2)$ and these histograms. For every $\delta>0$, at all sufficiently large integer scales $m$, and over every field $K$, there is a restriction
--   $$\bigoplus_{j=1}^{k}\langle d,d,d\rangle\preceq\operatorname{Cyc}(U_m),\qquad d=5^{4G+2L},$$
--   where $\operatorname{Cyc}$ denotes cyclic symmetrization and
--   $$\log k\ge2N\bigl((\log2)(\mathcal H_2(\beta_Z)+2)-\delta\bigr).$$
--   Here $\mathcal H_2$ is Shannon entropy in bits and the other logarithms are natural. Thus the square-matrix multiplicity achieves the first-slice entropy rate with arbitrarily small normalized loss. This is a quantitative extraction from the cyclically symmetrized literal intact source; the global cofinal stage construction and repair budgets are not asserted.
-- source:
--   Consequence of the accepted intact first-slice finite square extraction and the eventual sublinear logarithmic/square-root loss bound.

import Theorems.Thm_mme_more_asymmetry_first_112_intact_square_extractions
import Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear

open MME MME.CompleteSplit MME.CompleteSplit112 Filter
open CoupledCTensorPackaging
universe u
set_option autoImplicit false

theorem mme_more_asymmetry_first_112_intact_square_entropy_rate :
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
          ∀ (K : Type u) [Field K], ∃ k : ℕ,
            TensorObj.Restrict
              (TensorObj.bigAdd (fun _ : Fin k =>
                MMObj K (5 ^ (4 * G + 2 * L)) (5 ^ (4 * G + 2 * L))
                  (5 ^ (4 * G + 2 * L))))
              (cyclicSymmetrization
                (MME.RecursiveYZ.CWCells.unbroken K 5 2 (2 * N)
                  (Equiv.refl _) (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
                  (fun i _ => mu m i))) ∧
            ((2 * N : ℕ) : ℝ) *
                (Real.log 2 * (mme_modern_entropyBits (beta 2).probability + 2) - delta) ≤
              Real.log (k : ℝ) := by sorry
