-- Prove2me | Theorems.Thm_GoldbachActiveRoundedData_all_active_and_aligned_objectives_lt_ceiling
-- name    : GoldbachActiveRoundedData.all_active_and_aligned_objectives_lt_ceiling
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T03:34:10.62824+00:00
-- url     : https://prove2.me/theorems/d8f3e715-f29a-49d2-ab80-8d0b6891eb61
-- title:
--   Kernel-checked packet ceilings for all active and aligned scalar rows
-- statement:
--   Let $k$ select one of the 64 registered rows in `GoldbachActiveRoundedData`:
--   all 63 active packet rows and the aligned scalar row from the v4 release at
--   https://goldbach-nine.vercel.app/ . Write its integer cap sequences as $a_i,b_i$,
--   budgets as $U,V$, base-energy numerator as $B$, and $D=10^{12}$.
--
--   For any real number $q$ and real sequences $r_i,t_i$ satisfying
--
--   $$q\le B/D^2,\quad 0\le r_i\le a_i/D,\quad 0\le t_i\le b_i/D,$$
--
--   and every bounded partial-mass constraint
--
--   $$\sum_{i<n}r_i\le U/D,\qquad \sum_{i<n}t_i\le V/D,$$
--
--   the quadratic series converges and
--
--   $$q+\sum_{i=0}^{\infty}(r_i+t_i)^2<\frac{198479}{200000}.$$
--
--   The proof retains the supplied base-energy upper bound as an explicit premise.
--   It proves the known countable aligned cap-and-mass inequality, reduces its
--   greedy extremum to a finite prefix, and checks every cap ordering, budget cover,
--   and integer energy comparison using `decide +kernel`. It imports only the data
--   definition and Mathlib, with no open theorem or solution imports.
--
--   The registered data conservatively enlarges all corresponding frozen witness
--   constraints, as checked separately by exact Python arithmetic. This is a closed
--   optimization theorem conditional on those constraints. It does not establish
--   that analytic zero sums satisfy them, the paper's exceptional-set estimate, or
--   strong Goldbach. The optimization principle is attributed to Theorem 17 of
--   https://lorenzoschiavone.com/writing/goldbach-exceptional-set-bound/ . No
--   mathematical novelty is claimed.
-- source:
--   Conservative numerical certificate bounds for https://goldbach-nine.vercel.app/release/goldbach-exception-069697-certificate-v4.zip . Analytic input derivation remains separate; no mathematical novelty is claimed.

import Definitions.Def_GoldbachActiveRoundedData
import Mathlib.Topology.Algebra.InfiniteSum.Real
open scoped BigOperators
set_option autoImplicit false

theorem GoldbachActiveRoundedData.all_active_and_aligned_objectives_lt_ceiling (k : Fin 64) (q : ℝ) (r t : ℕ → ℝ)
    (hq : q ≤ ((GoldbachActiveRoundedData.row k).baseEnergy:ℝ)/
      (GoldbachActiveRoundedData.scale:ℝ)^2)
    (hr0 : ∀ i, 0 ≤ r i) (ht0 : ∀ i, 0 ≤ t i)
    (hra : ∀ i, r i ≤ (GoldbachActiveRoundedData.rcap k i:ℝ)/
      (GoldbachActiveRoundedData.scale:ℝ))
    (htb : ∀ i, t i ≤ (GoldbachActiveRoundedData.tcap k i:ℝ)/
      (GoldbachActiveRoundedData.scale:ℝ))
    (hrmass : ∀ n, (∑ i ∈ Finset.range n, r i) ≤
      ((GoldbachActiveRoundedData.row k).rBudget:ℝ)/(GoldbachActiveRoundedData.scale:ℝ))
    (htmass : ∀ n, (∑ i ∈ Finset.range n, t i) ≤
      ((GoldbachActiveRoundedData.row k).tBudget:ℝ)/(GoldbachActiveRoundedData.scale:ℝ)) :
    Summable (fun i => (r i+t i)^2) ∧ q+(∑' i, (r i+t i)^2) < (198479:ℝ)/200000 := by sorry
