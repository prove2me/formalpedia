-- Prove2me | Theorems.Thm_section5_matrix_net_tail
-- name    : section5_matrix_net_tail
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T22:16:33.477799+00:00
-- url     : https://prove2.me/theorems/bd71f62e-7b61-5f92-beec-518ee0331fb9
-- title:
--   Operator-norm tail bound from finite quarter-nets
-- statement:
--   Let $A$ be a random real $m\times n$ matrix on a finite measure space, with $m,n>0$. Let $N$ and $M$ be finite $1/4$-nets contained in the respective unit spheres. Suppose every pair of net directions satisfies
--   $$\mu\{\langle Ax,y\rangle>t\}\le\delta.$$
--   Then
--   $$\mu\{\|A\|_{\mathrm{op}}>2t\}\le |N|\,|M|\,\delta.$$
--   No independence among the directional events is assumed. The thresholds $t$ and $\delta$ are arbitrary real numbers; any impossible hypotheses remain explicit. The same argument applies to a centered sample-covariance estimator, once its directional tails have been established.
--
--   This is a concentration bridge for the Section 5 tomography work, not a construction of the quantum measurement or a proof of Theorem 5.6.
-- source:
--   Standard finite-net argument and finite union bound; builds on the accepted quadratic-form comparison by mrfancypants (submission 1b7cac7e-267f-4bb7-bf43-33234a55f00c), exposed as section5_quadratic_form_on_net (theorem e6ba8fc7-99a6-5726-991e-fe8dd5272d73). Application context: Krivcenko, Nguyen, de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.4. This general tail formulation is a supporting derivation, not a numbered claim quoted from the paper.

import Theorems.Thm_section5_quadratic_form_on_net
set_option autoImplicit false
open MeasureTheory HighDimProb.RandomMatrices

theorem section5_matrix_net_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {m n : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (N : Finset (EuclideanSpace ℝ (Fin n)))
    (M : Finset (EuclideanSpace ℝ (Fin m)))
    (hN : IsEpsNet (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (↑N) (1/4))
    (hM : IsEpsNet (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) (↑M) (1/4))
    (t δ : ℝ)
    (htail : ∀ x ∈ N, ∀ y ∈ M,
      μ.real {ω | t < inner ℝ (Matrix.toEuclideanLin (A ω) x) y} ≤ δ) :
    μ.real {ω | 2*t < matrixOpNorm (A ω)} ≤ (N.card : ℝ)*(M.card : ℝ)*δ := by sorry
