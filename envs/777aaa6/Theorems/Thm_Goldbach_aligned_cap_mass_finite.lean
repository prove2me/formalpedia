-- Prove2me | Theorems.Thm_Goldbach_aligned_cap_mass_finite
-- name    : Goldbach.aligned_cap_mass_finite
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T02:13:49.327854+00:00
-- url     : https://prove2.me/theorems/111c5579-5ba1-4d68-a8da-473656b7e878
-- title:
--   Finite aligned cap-and-mass bound with separate coordinate budgets
-- statement:
--   Let $n\ge0$ and let $(a_i)_{0\le i<n}$ and $(b_i)_{0\le i<n}$ be decreasing real cap sequences. Suppose
--   $$0\le r_i\le a_i,\qquad 0\le t_i\le b_i,\qquad
--     \sum_{i<n}r_i\le U,\qquad \sum_{i<n}t_i\le V.$$
--   Define the aligned greedy fills by
--   $$g_i^R=\min\left\{a_i,\max\left(0,U-\sum_{j<i}a_j\right)\right\},\qquad
--     g_i^T=\min\left\{b_i,\max\left(0,V-\sum_{j<i}b_j\right)\right\}.$$
--   Then
--   $$\sum_{i<n}(r_i+t_i)^2\le\sum_{i<n}(g_i^R+g_i^T)^2.$$
--
--   This is the finite inequality in Theorem 17 of Lorenzo Schiavone's
--   [A computer-assisted 23/33 + epsilon bound for the exceptional set in the binary Goldbach problem](https://lorenzoschiavone.com/writing/goldbach-exceptional-set-bound/).
--   The input coordinates need not be sorted. Retaining both budgets in the same coordinate order controls their coupled quadratic objective. This formalization establishes the elementary finite inequality, without claiming mathematical novelty, attainment, the countable case, or verification of the manuscript's analytic inputs or exceptional-set conclusion.
--
--   Formalization note: The proof is self-contained in Mathlib revision `777aaa61dcd2a1258d2b4962dbe983ede4d23b2e` and has only standard axioms.
-- source:
--   Finite version of Theorem 17 (Aligned cap-and-mass lemma) in Lorenzo Schiavone, A computer-assisted 23/33 + epsilon bound for the exceptional set in the binary Goldbach problem, July 18 2026: https://lorenzoschiavone.com/writing/goldbach-exceptional-set-bound/ . Formalizes the elementary finite inequality only; no claim of literature novelty, countable extension, or verification of the full analytic paper.

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
open scoped BigOperators
set_option autoImplicit false

theorem Goldbach.aligned_cap_mass_finite (n : ℕ) (a b r t : Fin n → ℝ) (U V : ℝ)
    (ha : Antitone a) (hb : Antitone b)
    (hr0 : ∀ i, 0 ≤ r i) (ht0 : ∀ i, 0 ≤ t i)
    (hra : ∀ i, r i ≤ a i) (htb : ∀ i, t i ≤ b i)
    (hrmass : (∑ i, r i) ≤ U) (htmass : (∑ i, t i) ≤ V) :
    (∑ i, (r i+t i)^2) ≤ ∑ i,
      (min (a i) (max 0 (U - ∑ j : Fin n, if j.val < i.val then a j else 0)) +
       min (b i) (max 0 (V - ∑ j : Fin n, if j.val < i.val then b j else 0)))^2 := by sorry
