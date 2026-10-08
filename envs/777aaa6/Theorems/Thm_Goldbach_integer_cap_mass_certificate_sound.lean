-- Prove2me | Theorems.Thm_Goldbach_integer_cap_mass_certificate_sound
-- name    : Goldbach.integer_cap_mass_certificate_sound
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T02:53:58.93722+00:00
-- url     : https://prove2.me/theorems/bed2ff5a-4d85-433b-b04c-1a0ff1911684
-- title:
--   Integer certificate soundness for a countable cap-and-mass objective
-- statement:
--   Let $(A_i)$ and $(B_i)$ be decreasing sequences of nonnegative integers. Let $U,V,D,N,M,K$ be nonnegative integers with $D,K>0$. Assume
--   $$U\le\sum_{i<N}A_i,\qquad V\le\sum_{i<N}B_i.$$
--   Define the integer greedy fills
--   $$G_i=\min\left\{A_i,\max\left(0,U-\sum_{j<i}A_j\right)\right\},\qquad
--     H_i=\min\left\{B_i,\max\left(0,V-\sum_{j<i}B_j\right)\right\}.$$
--   Suppose the finite integer certificate satisfies
--   $$K\sum_{i<N}(G_i+H_i)^2<MD^2.$$
--   For any nonnegative real sequences $(r_i),(t_i)$ with
--   $$r_i\le A_i/D,\qquad t_i\le B_i/D,\qquad
--    \sum_{i<n}r_i\le U/D,\qquad \sum_{i<n}t_i\le V/D\quad(n\ge0),$$
--   the quadratic series converges and
--   $$\sum_{i=0}^{\infty}(r_i+t_i)^2<M/K.$$
--
--   This converts finite integer checks into a rigorous bound on a countable optimization problem. Untrusted programs can propose the cap and budget data; the certificate condition can then be checked by kernel computation. The result follows from the aligned cap-and-mass inequality of [Schiavone's Theorem 17](https://lorenzoschiavone.com/writing/goldbach-exceptional-set-bound/). It does not derive analytic cap or budget estimates.
--
--   Formalization note: The proof is self-contained in Mathlib revision `777aaa61dcd2a1258d2b4962dbe983ede4d23b2e` and has only standard axioms. No mathematical novelty is claimed.
-- source:
--   An integer certificate interface derived from the aligned cap-and-mass inequality, Theorem 17, https://lorenzoschiavone.com/writing/goldbach-exceptional-set-bound/ . No mathematical novelty or analytic cap derivation is claimed.

import Mathlib.Topology.Algebra.InfiniteSum.Real
open scoped BigOperators
set_option autoImplicit false

theorem Goldbach.integer_cap_mass_certificate_sound (a b : ℕ → ℕ) (U V D N M K : ℕ)
    (hD : 0 < D) (hK : 0 < K) (ha : Antitone a) (hb : Antitone b)
    (hcoverR : U ≤ ∑ i ∈ Finset.range N, a i)
    (hcoverT : V ≤ ∑ i ∈ Finset.range N, b i)
    (hcalc : K*(∑ i ∈ Finset.range N,
      (min (a i) (U - ∑ j ∈ Finset.range i, a j) +
       min (b i) (V - ∑ j ∈ Finset.range i, b j))^2) < M*D^2)
    (r t : ℕ → ℝ) (hr0 : ∀ i, 0 ≤ r i) (ht0 : ∀ i, 0 ≤ t i)
    (hra : ∀ i, r i ≤ (a i:ℝ)/(D:ℝ))
    (htb : ∀ i, t i ≤ (b i:ℝ)/(D:ℝ))
    (hrmass : ∀ n, (∑ i ∈ Finset.range n, r i) ≤ (U:ℝ)/(D:ℝ))
    (htmass : ∀ n, (∑ i ∈ Finset.range n, t i) ≤ (V:ℝ)/(D:ℝ)) :
    Summable (fun i => (r i+t i)^2) ∧ (∑' i, (r i+t i)^2) < (M:ℝ)/(K:ℝ) := by sorry
