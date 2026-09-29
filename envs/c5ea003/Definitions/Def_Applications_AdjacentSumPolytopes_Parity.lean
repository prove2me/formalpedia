-- Prove2me | Definitions.Def_Applications_AdjacentSumPolytopes_Parity
-- name    : Applications_AdjacentSumPolytopes_Parity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:27:15.221394+00:00
-- url     : https://prove2.me/theorems/328e1a4e-88da-4f76-beb9-3d5a3867c01b
-- title:
--   Aether Catalog definitions — Applications_AdjacentSumPolytopes_Parity
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.AdjacentSumPolytopes.Parity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/AdjacentSumPolytopes/Parity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Basic
import Definitions.Def_Applications_AdjacentSumPolytopes_Growth

/-!
# Parity classes: even counts are sums of squares, and both classes are log-convex

The transfer matrix `adjMat s` is symmetric.  This forces two structural facts that link
the two parity classes of the adjacent-sum model:

* **Even = sum of squares.**  A cyclic count of *even* length `2k` is the squared
  Frobenius norm of the `k`-th power of the transfer matrix, and an open count of even
  length is the squared Euclidean norm of the vector of row sums
  (`cycCount_even_eq_sum_sq`, `openCount_even_eq_sum_sq`).
* **Log-convexity.**  Cauchy–Schwarz then gives
  `c(m+n)² ≤ c(2m) · c(2n)` for both the cyclic and the open counting sequences
  (`cycCount_sq_le`, `openCount_sq_le`): each odd-index count is controlled by the two
  neighbouring even-index counts.  Equivalently, `k ↦ log c(k)` is midpoint convex along
  the even/odd interleaving, so the even class dominates the odd class.

These are exactly the statements that make the two parity classes comparable even though
their generating-function *numerators* differ (the denominator being shared, by
`Applications.AdjacentSumPolytopes.Recurrence`).

-- !-- Lab Notes -- !--
* **Hypothesis.** Symmetry of the constraint `a + b ≤ s` should make even-length counts
  sums of squares, hence force a Cauchy–Schwarz relation between the parity classes.
* **Experiment.** `s = 2`: cyclic counts `c(d) = #cyclic of length d+1` are
  `2, 6, 11, 26, 57, 129, 289`.  Testing `c(p+q+1)² ≤ c(2p+1)·c(2q+1)` at `p = 0, q = 1`:
  `c(2)² = 121 ≤ c(1)·c(3) = 6·26 = 156` ✓; at `p = 1, q = 2`: `c(4)² = 3249 ≤
  c(3)·c(5) = 26·129 = 3354` ✓ — tight but valid.  Open counts `3, 6, 14, 31, 70, 157`:
  `o(3)² = 961 ≤ o(2)·o(4) = 14·70 = 980` ✓.
* **Analysis.** The margin shrinks as `d` grows, as it must: log-convexity is asymptotically
  an equality for a sequence dominated by a single exponential.  This is independent
  evidence for a *simple* dominant pole.
* **Critique.** Both inequalities are proved for all `s` and all `m, n` with no hypotheses;
  the equality cases (`m = n`) are genuine equalities, so the bound cannot be improved
  to a strict inequality.
-/

namespace AdjSum

open Finset Matrix

variable {s : ℕ}


/-! ## Even counts as sums of squares -/



/-- The row sums of the powers of the transfer matrix. -/
def rowSum (s k : ℕ) (c : Fin (s + 1)) : ℕ := ∑ b, (adjMat s ^ k) c b



/-! ## Log-convexity of both parity classes -/




end AdjSum


