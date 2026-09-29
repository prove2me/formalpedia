-- Prove2me | Theorems.Thm_tropp_even_schatten_variance_scale
-- name    : tropp_even_schatten_variance_scale
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-25T06:39:50.214707+00:00
-- url     : https://prove2.me/theorems/b94c3e90-5135-45cb-b123-5c258e7dd0c1
-- statement:
--   Tropp-route even-Schatten variance-scale moment bound (noncommutative Khintchine via the Tropp/Buchholz matrix moment recursion, bypassing Lust-Picquard duality). For a Rademacher-symmetrized sampled matrix and even exponent $2n$ ($n\ge1$), the Rademacher expectation of $\lVert\cdot\rVert_{S_{2n}}^{2n}$ is at most $\frac{(2n)!}{2^n n!}\,(\text{varianceScale})^{2n}(n_1+n_2)$, where $\frac{(2n)!}{2^n n!}=(2n-1)!!$ is the Buchholz pairing-count (double-factorial) constant. This is the trace-moment self-bounding recursion giving the $\sqrt q$ Khintchine factor at even integer order.
-- source:
--   Tropp, User-friendly tail bounds for matrix sums; CR2008 Section 6.1; Buchholz Math. Ann. 2001

import Definitions.Def_matrix_completion_schatten
import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion

theorem tropp_even_schatten_variance_scale {n1 n2 : ℕ}
    (n : ℕ) (hn : 1 ≤ n)
    (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    rademacherExpectation
        (fun eps => schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ (2 * n))
      ≤ ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ)))
          * (rademacherSampledVarianceScale Omega p X) ^ (2 * n)
          * ((n1 : ℝ) + (n2 : ℝ)) := by
  sorry
