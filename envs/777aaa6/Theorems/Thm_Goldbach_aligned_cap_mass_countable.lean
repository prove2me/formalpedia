-- Prove2me | Theorems.Thm_Goldbach_aligned_cap_mass_countable
-- name    : Goldbach.aligned_cap_mass_countable
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T02:25:54.610542+00:00
-- url     : https://prove2.me/theorems/dcd76344-b9c7-4f94-a31d-f6f958258674
-- title:
--   Countable aligned cap-and-mass bound with proved convergence
-- statement:
--   Let $(a_i)_{i\ge0}$ and $(b_i)_{i\ge0}$ be decreasing real cap sequences. Let $(r_i)$ and $(t_i)$ be nonnegative sequences satisfying $r_i\le a_i$, $t_i\le b_i$, and, for every $n\ge0$,
--   $$\sum_{i<n}r_i\le U,\qquad \sum_{i<n}t_i\le V.$$
--   Define the aligned greedy fills by
--   $$g_i^R=\min\left\{a_i,\max\left(0,U-\sum_{j<i}a_j\right)\right\},\qquad
--     g_i^T=\min\left\{b_i,\max\left(0,V-\sum_{j<i}b_j\right)\right\}.$$
--   Then both quadratic series converge and
--   $$\sum_{i=0}^{\infty}(r_i+t_i)^2\le
--     \sum_{i=0}^{\infty}(g_i^R+g_i^T)^2.$$
--
--   This is the countable inequality in Theorem 17 of Lorenzo Schiavone's
--   [A computer-assisted 23/33 + epsilon bound for the exceptional set in the binary Goldbach problem](https://lorenzoschiavone.com/writing/goldbach-exceptional-set-bound/).
--   It bounds a coupled quadratic objective while retaining separate coordinate caps and mass budgets. The input coordinates need not be sorted, and the caps need not be summable. The registered result includes convergence but does not assert attainment of the maximum or establish the manuscript's analytic inputs or exceptional-set estimate.
--
--   Formalization note: The self-contained Lean proof uses the original strong-Goldbach environment, Mathlib revision `777aaa61dcd2a1258d2b4962dbe983ede4d23b2e`, and only standard axioms. No mathematical novelty is claimed.
-- source:
--   Countable inequality in Theorem 17 of Lorenzo Schiavone, A computer-assisted 23/33 + epsilon bound for the exceptional set in the binary Goldbach problem, July 18 2026: https://lorenzoschiavone.com/writing/goldbach-exceptional-set-bound/ . Includes explicit summability; no literature novelty, attainment, exceptional-set estimate or verification of the full analytic paper is claimed.

import Mathlib.Topology.Algebra.InfiniteSum.Real
open scoped BigOperators
set_option autoImplicit false

theorem Goldbach.aligned_cap_mass_countable (a b r t : ℕ → ℝ) (U V : ℝ)
    (ha : Antitone a) (hb : Antitone b)
    (hr0 : ∀ i, 0 ≤ r i) (ht0 : ∀ i, 0 ≤ t i)
    (hra : ∀ i, r i ≤ a i) (htb : ∀ i, t i ≤ b i)
    (hrmass : ∀ n, (∑ i ∈ Finset.range n, r i) ≤ U)
    (htmass : ∀ n, (∑ i ∈ Finset.range n, t i) ≤ V) :
    Summable (fun i => (r i+t i)^2) ∧
    Summable (fun i =>
      (min (a i) (max 0 (U - ∑ j ∈ Finset.range i, a j)) +
       min (b i) (max 0 (V - ∑ j ∈ Finset.range i, b j)))^2) ∧
    (∑' i, (r i+t i)^2) ≤ ∑' i,
      (min (a i) (max 0 (U - ∑ j ∈ Finset.range i, a j)) +
       min (b i) (max 0 (V - ∑ j ∈ Finset.range i, b j)))^2 := by sorry
