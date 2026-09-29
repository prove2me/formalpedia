-- Prove2me | Theorems.Thm_rademacher_sampled_trace_eq_buchholz_signed_walk_sum
-- name    : rademacher_sampled_trace_eq_buchholz_signed_walk_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-23T23:19:33.375333+00:00
-- url     : https://prove2.me/theorems/4d211508-693a-47cf-b2e0-7d44f436bb91
-- statement:
--   **Pointwise trace-power expansion for the sampled Rademacher matrix.** Fix a sign assignment $\varepsilon$ and write
--   $$S_\varepsilon=p^{-1}\sum_{(i,j)\in\Omega}\varepsilon_{ij}X_{ij}e_i e_j^{\top}.$$
--   For every integer $n\ge1$, the trace $\operatorname{tr}((S_\varepsilon S_\varepsilon^{\top})^n)$ expands as the alternating row/column closed-walk sum $\widetilde W_n(\varepsilon;\Omega,p,X)$.
--
--   In walk notation, the factors are $S_{i_kj_k}$ and $S_{i_{k+1}j_k}$ around the cycle
--   $$i_0-j_0-i_1-j_1-\cdots-i_{n-1}-j_{n-1}-i_0.$$
--   This is the pointwise matrix-entry K-expand leaf.  It is intended to be proved from the existing `trace_pow_eq_walk` theorem plus the definition of matrix multiplication and transpose.
-- source:
--   Buchholz, A. "Operator Khintchine inequality in non-commutative probability." Math. Ann. 319 (2001): 1-16, Section 2; Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119, Section 6.1 Lemma 6.1.

import Definitions.Def_buchholz_signed_walk_sum

open MatrixCompletion
open scoped BigOperators

theorem rademacher_sampled_trace_eq_buchholz_signed_walk_sum
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega eps : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    Matrix.trace
        ((rademacherSampledMatrix Omega eps p X *
            (rademacherSampledMatrix Omega eps p X).transpose) ^ n)
      = buchholzSignedWalkSum n Omega p X eps := by
  sorry
