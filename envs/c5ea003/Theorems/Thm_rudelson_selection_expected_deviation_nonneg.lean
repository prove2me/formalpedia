-- Prove2me | Theorems.Thm_rudelson_selection_expected_deviation_nonneg
-- name    : rudelson_selection_expected_deviation_nonneg
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-06-23T23:39:29.566483+00:00
-- url     : https://prove2.me/theorems/db429d8a-60b7-4182-87e5-e87a8c6c1dc8
-- statement:
--   Nonnegativity of the Rudelson selection expected deviation. $EZ=\mathbb E_p\,\mathrm{tangentSamplingDeviation}(\Omega,S,p)$ is a Bernoulli-weighted sum; each weight is nonnegative for $0\le p\le 1$, and each deviation is the supremum of nonnegative quantities $p^{-1}\lVert\cdot\rVert_F\ge 0$, so the whole expectation is nonnegative.
-- source:
--   Candes-Recht 2009 (arXiv:0805.4471) Section 4.2; bernoulliExpectation/tangentSamplingDeviation definitions.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion
open scoped Classical BigOperators

theorem rudelson_selection_expected_deviation_nonneg {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (S : SVD M r) {p : Real} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ bernoulliExpectation p (fun Omega => tangentSamplingDeviation Omega S p) := by sorry
