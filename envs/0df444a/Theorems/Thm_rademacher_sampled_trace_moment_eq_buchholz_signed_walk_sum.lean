-- Prove2me | Theorems.Thm_rademacher_sampled_trace_moment_eq_buchholz_signed_walk_sum
-- name    : rademacher_sampled_trace_moment_eq_buchholz_signed_walk_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-23T23:06:02.893103+00:00
-- url     : https://prove2.me/theorems/d8057f13-e756-477e-b78d-20b721b9ed0e
-- statement:
--   **Trace-power expansion to the raw signed walk sum.** For a fixed sampled coordinate Rademacher matrix
--   $$S_\varepsilon=p^{-1}\sum_{(i,j)\in\Omega}\varepsilon_{ij}X_{ij}e_i e_j^{\top},$$
--   the trace $\operatorname{tr}((S_\varepsilon S_\varepsilon^{\top})^n)$ expands over alternating closed row/column walks.  The coefficient of a walk is the product of the sampled entries $p^{-1}\delta_{ij}X_{ij}$ times the sign monomial from all traversed coordinate edges.
--
--   This theorem states that, after averaging over $\varepsilon$, the original trace moment equals the expectation of the raw signed-walk sum $\widetilde W_n(\varepsilon;\Omega,p,X)$.  It is the pure matrix-entry K-expand layer; no sign cancellation or Buchholz counting is used here.
-- source:
--   Buchholz, A. "Operator Khintchine inequality in non-commutative probability." Math. Ann. 319 (2001): 1-16, Section 2; Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119, Section 6.1 Lemma 6.1.

import Definitions.Def_buchholz_signed_walk_sum

open MatrixCompletion
open scoped BigOperators

theorem rademacher_sampled_trace_moment_eq_buchholz_signed_walk_sum
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    rademacherExpectation
        (fun eps =>
          Matrix.trace
            ((rademacherSampledMatrix Omega eps p X *
                (rademacherSampledMatrix Omega eps p X).transpose) ^ n))
      =
    rademacherExpectation
        (fun eps => buchholzSignedWalkSum n Omega p X eps) := by
  sorry
