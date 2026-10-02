-- Prove2me | Theorems.Thm_BookSixth_ramsey_real_bound
-- name    : BookSixth.ramsey_real_bound
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-13T01:37:09.16138+00:00
-- url     : https://prove2.me/theorems/2bfb9361-ae39-4aa2-8638-e42677d27f2f
-- title:
--   Chapter 45, Theorem 2: Ramsey exponential bound
-- statement:
--   For k at least 2 and every natural N smaller than 2^(k/2) with real exponent, a graph on N vertices has neither a clique nor an independent set of size k. This is the existence formulation of R(k,k)≥2^(k/2); it preserves the real exponent for odd k.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 45, Theorem 2: Ramsey exponential bound, p. 313. https://doi.org/10.1007/978-3-662-57265-8_45

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.ramsey_real_bound (k N : ℕ) (hk : 2 ≤ k) (hN : (N : ℝ) < (2 : ℝ)^((k : ℝ)/2)) :
    ∃ G : SimpleGraph (Fin N), NoMono k G := by sorry
