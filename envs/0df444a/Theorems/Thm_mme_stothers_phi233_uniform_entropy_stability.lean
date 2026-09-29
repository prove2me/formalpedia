-- Prove2me | Theorems.Thm_mme_stothers_phi233_uniform_entropy_stability
-- name    : mme_stothers_phi233_uniform_entropy_stability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:44:16.286323+00:00
-- url     : https://prove2.me/theorems/f9ac89f8-acd1-49de-aa19-2e2903661ca7
-- title:
--   Uniform asymptotic entropy stability for phi_233 completions
-- statement:
--   Let $(a,b,c,d)$ be a positive normalized stationary $\varphi_{233}$ profile. Suppose target profiles $(A_n,B_n,C_n,D_n)$ converge coordinatewise to it. For each $n$, let $(X_n,Y_n,Z_n,W_n)$ be any nonnegative normalized competitor with the same two independent marginals as the target profile:
--
--   $$
--   2X_n+Y_n=2A_n+B_n,\qquad X_n+Z_n=A_n+C_n.
--   $$
--
--   Writing $T(u,v,w,z)=4h(u/2)+2h(v/2)+2h(w/2)+2h(z/2)$ for $h(x)=-x\log x$, for every $\varepsilon>0$ one eventually has
--
--   $$
--   T(X_n,Y_n,Z_n,W_n)\le T(A_n,B_n,C_n,D_n)+\varepsilon.
--   $$
--
--   The estimate is uniform over the competing profile at every scale. It rigorously justifies replacing the full same-marginal entropy maximum by the rounded target-profile entropy with a vanishing asymptotic loss in the exceptional $\varphi_{233}$ extraction.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Equation (3.6) and Lemma 5.1(v), pp. 360 and 366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; this theorem makes explicit the vanishing entropy loss in the paper's limiting profile argument.

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Algebra.Order.Field
import Theorems.Thm_mme_stothers_phi233_entropy_tangent_stability

open Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_stothers_phi233_uniform_entropy_stability
    (a b c d : ℝ) (A B C D X Y Z W : ℕ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (htotal : 2 * a + b + c + d = 1)
    (hstation :
      2 * (-Real.log (a / 2) - 1) -
          2 * (-Real.log (b / 2) - 1) -
          (-Real.log (c / 2) - 1) +
          (-Real.log (d / 2) - 1) = 0)
    (hA : Tendsto A atTop (nhds a))
    (hB : Tendsto B atTop (nhds b))
    (hC : Tendsto C atTop (nhds c))
    (hD : Tendsto D atTop (nhds d))
    (hX : ∀ n, 0 ≤ X n) (hY : ∀ n, 0 ≤ Y n)
    (hZ : ∀ n, 0 ≤ Z n) (hW : ∀ n, 0 ≤ W n)
    (htotalX : ∀ n, 2 * X n + Y n + Z n + W n = 1)
    (hsigmaX : ∀ n, 2 * X n + Y n = 2 * A n + B n)
    (hmuX : ∀ n, X n + Z n = A n + C n) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        4 * Real.negMulLog (X n / 2) +
              2 * Real.negMulLog (Y n / 2) +
              2 * Real.negMulLog (Z n / 2) +
              2 * Real.negMulLog (W n / 2) ≤
          4 * Real.negMulLog (A n / 2) +
              2 * Real.negMulLog (B n / 2) +
              2 * Real.negMulLog (C n / 2) +
              2 * Real.negMulLog (D n / 2) + ε := by
  sorry
