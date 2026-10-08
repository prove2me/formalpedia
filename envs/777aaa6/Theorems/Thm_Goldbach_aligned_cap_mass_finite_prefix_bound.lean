-- Prove2me | Theorems.Thm_Goldbach_aligned_cap_mass_finite_prefix_bound
-- name    : Goldbach.aligned_cap_mass_finite_prefix_bound
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T02:32:26.153033+00:00
-- url     : https://prove2.me/theorems/ab11d49e-ddd7-4e05-b6ca-3f3920b02feb
-- title:
--   A finite certificate bound for a countable aligned cap-and-mass objective
-- statement:
--   Let $(a_i)$ and $(b_i)$ be decreasing real cap sequences, and let $(r_i)$ and $(t_i)$ satisfy
--   $$0\le r_i\le a_i,\qquad 0\le t_i\le b_i,\qquad
--     \sum_{i<n}r_i\le U,\qquad \sum_{i<n}t_i\le V\quad(n\ge0).$$
--   Suppose a finite prefix covers both budgets:
--   $$U\le\sum_{i<N}a_i,\qquad V\le\sum_{i<N}b_i.$$
--   Define the aligned greedy fills
--   $$g_i^R=\min\left\{a_i,\max\left(0,U-\sum_{j<i}a_j\right)\right\},\qquad
--     g_i^T=\min\left\{b_i,\max\left(0,V-\sum_{j<i}b_j\right)\right\}.$$
--   Then the quadratic series converges and has the finite upper bound
--   $$\sum_{i=0}^{\infty}(r_i+t_i)^2\le\sum_{i<N}(g_i^R+g_i^T)^2.$$
--
--   This corollary of the aligned cap-and-mass inequality reduces a countable optimization bound to a finite calculation. The input sequences can have infinite support: it is the extremal greedy fills that vanish beyond the covered prefix. With rational boundary data, the remaining upper bound admits an exact rational certificate.
--
--   The underlying majorization result is Theorem 17 in [Lorenzo Schiavone's manuscript](https://lorenzoschiavone.com/writing/goldbach-exceptional-set-bound/). This elementary formalization does not derive the analytic caps or mass budgets required in a Goldbach application.
--
--   Formalization note: The self-contained proof uses Mathlib revision `777aaa61dcd2a1258d2b4962dbe983ede4d23b2e`, includes summability, and has only standard axioms. No mathematical novelty is claimed.
-- source:
--   Elementary finite-support corollary of the countable inequality in Theorem 17, Lorenzo Schiavone: https://lorenzoschiavone.com/writing/goldbach-exceptional-set-bound/ . Proves that a cap prefix covering both budgets suffices to bound the full countable objective; no mathematical novelty or verification of analytic inputs is claimed.

import Mathlib.Topology.Algebra.InfiniteSum.Real
open scoped BigOperators
set_option autoImplicit false

theorem Goldbach.aligned_cap_mass_finite_prefix_bound (a b r t : ℕ → ℝ) (U V : ℝ) (N : ℕ)
    (ha : Antitone a) (hb : Antitone b)
    (hr0 : ∀ i, 0 ≤ r i) (ht0 : ∀ i, 0 ≤ t i)
    (hra : ∀ i, r i ≤ a i) (htb : ∀ i, t i ≤ b i)
    (hrmass : ∀ n, (∑ i ∈ Finset.range n, r i) ≤ U)
    (htmass : ∀ n, (∑ i ∈ Finset.range n, t i) ≤ V)
    (hcoverR : U ≤ ∑ i ∈ Finset.range N, a i)
    (hcoverT : V ≤ ∑ i ∈ Finset.range N, b i) :
    Summable (fun i => (r i+t i)^2) ∧
    (∑' i, (r i+t i)^2) ≤ ∑ i ∈ Finset.range N,
      (min (a i) (max 0 (U - ∑ j ∈ Finset.range i, a j)) +
       min (b i) (max 0 (V - ∑ j ∈ Finset.range i, b j)))^2 := by sorry
