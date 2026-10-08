-- Prove2me | Theorems.Thm_GoldbachSecondaryRoundedData_all_secondary_objectives_lt_ceiling
-- name    : GoldbachSecondaryRoundedData.all_secondary_objectives_lt_ceiling
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T03:11:19.609993+00:00
-- url     : https://prove2.me/theorems/b2755ec4-962f-4455-b2df-ca9d0205225d
-- title:
--   A kernel-checked optimization ceiling for all sixteen rounded secondary rows
-- statement:
--   For any one of the sixteen records in the fixed secondary certificate data, let $(A_i)$ and $(B_i)$ be its integer cap sequences, $U,V$ its integer budgets, and $D=10^{12}$ the common scale. Let $(r_i),(t_i)$ be arbitrary nonnegative real sequences satisfying
--   $$r_i\le A_i/D,\qquad t_i\le B_i/D,\qquad
--     \sum_{i<n}r_i\le U/D,\qquad\sum_{i<n}t_i\le V/D\quad(n\ge0).$$
--   Then the quadratic series converges and
--   $$\sum_{i=0}^{\infty}(r_i+t_i)^2<\frac{198479}{200000}.$$
--
--   The same strict ceiling holds for every record, including the limiting secondary row. These fixed data are conservative integer-grid enlargements of the sixteen finite secondary optimization witnesses in [Schiavone's certificate release](https://goldbach-nine.vercel.app/). The cap ordering, budget coverage, and integer objective inequalities are checked in the Lean kernel. The input sequences may have infinite support.
--
--   This establishes the numerical optimization bound for the registered rounded data. Exact Python comparisons establish the upward-enclosure correspondence with the frozen witness; the theorem does not derive those analytic inputs from zero-density estimates or establish the manuscript's exceptional-set conclusion.
--
--   Formalization note: The proof uses only the published data module and Mathlib revision `777aaa61dcd2a1258d2b4962dbe983ede4d23b2e`. All mathematical lemmas are closed with standard axioms; no open theorem or native decision procedure is imported.
-- source:
--   Numerical optimization bound for conservative enlargements of all sixteen secondary rows in https://goldbach-nine.vercel.app/release/goldbach-exception-069697-certificate-v4.zip . Reuses the known aligned cap-and-mass inequality; all finite integer conditions are checked with decide +kernel. Does not derive the analytic boundary inputs.

import Definitions.Def_GoldbachSecondaryRoundedData
import Mathlib.Topology.Algebra.InfiniteSum.Real
open scoped BigOperators
set_option autoImplicit false

theorem GoldbachSecondaryRoundedData.all_secondary_objectives_lt_ceiling (k : Fin 16) (r t : ℕ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (ht0 : ∀ i, 0 ≤ t i)
    (hra : ∀ i, r i ≤ (GoldbachSecondaryRoundedData.rcap k i:ℝ)/
      (GoldbachSecondaryRoundedData.scale:ℝ))
    (htb : ∀ i, t i ≤ (GoldbachSecondaryRoundedData.tcap k i:ℝ)/
      (GoldbachSecondaryRoundedData.scale:ℝ))
    (hrmass : ∀ n, (∑ i ∈ Finset.range n, r i) ≤
      ((GoldbachSecondaryRoundedData.row k).rBudget:ℝ)/(GoldbachSecondaryRoundedData.scale:ℝ))
    (htmass : ∀ n, (∑ i ∈ Finset.range n, t i) ≤
      ((GoldbachSecondaryRoundedData.row k).tBudget:ℝ)/(GoldbachSecondaryRoundedData.scale:ℝ)) :
    Summable (fun i => (r i+t i)^2) ∧ (∑' i, (r i+t i)^2) < (198479:ℝ)/200000 := by sorry
