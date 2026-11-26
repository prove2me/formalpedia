-- Prove2me | Theorems.Thm_section5_quadratic_form_on_net
-- name    : section5_quadratic_form_on_net
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:54:47.451289+00:00
-- url     : https://prove2.me/theorems/e6ba8fc7-99a6-5726-991e-fe8dd5272d73
-- title:
--   Operator norm comparison on Euclidean sphere nets
-- statement:
--   Let m,n>0, A∈R^(m×n), and 0≤ε<1/2. Let N,M be ε-nets contained in the unit spheres of R^n and R^m, respectively. Put S=sup{⟨Ax,y⟩:x∈N,y∈M}. Then $$S\le\|A\|_{\mathrm{op}}\le\frac{S}{1-2\varepsilon}.$$
-- source:
--   Reused net comparison by mrfancypants, accepted Prove2Me submission 1b7cac7e-267f-4bb7-bf43-33234a55f00c for theorem 66e14664-6067-4d0b-b3c2-4958d11db063. Exact local formalization: Solutions/Section5QuadraticNetFoundation.lean, lines 30–39. Used as a foundation for Section 5 of Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3; the copied result is not a new contribution.

import Definitions.Def_HighDimProb_RandomMatrices_IsEpsNet
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Mathlib
set_option autoImplicit false
open HighDimProb.RandomMatrices

theorem section5_quadratic_form_on_net {m n : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin m) (Fin n) ℝ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    (N : Set (EuclideanSpace ℝ (Fin n)))
    (hN : IsEpsNet (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) N ε)
    (M : Set (EuclideanSpace ℝ (Fin m)))
    (hM : IsEpsNet (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) M ε) :
    sSup (Set.image2 (fun x y => inner ℝ (Matrix.toEuclideanLin A x) y) N M)
        ≤ matrixOpNorm A ∧
    matrixOpNorm A ≤ (1 / (1 - 2 * ε)) *
        sSup (Set.image2 (fun x y => inner ℝ (Matrix.toEuclideanLin A x) y) N M) := by sorry
