-- Prove2me | Theorems.Thm_hurwitz_nonvanishing_limit
-- name    : hurwitz_nonvanishing_limit
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-06T17:57:01.041152+00:00
-- url     : https://prove2.me/theorems/62b01429-216b-408d-ac01-b51079ff4bf3
-- title:
--   Hurwitz theorem for uniform limits of non-vanishing holomorphic functions
-- statement:
--   Hurwitz's theorem on uniform limits of non-vanishing holomorphic functions. Let $U \subseteq \mathbb{C}$ be an open, preconnected set and let $(f_n)_{n \in \mathbb{N}}$ be a sequence of holomorphic functions $f_n : U \to \mathbb{C}$ converging to $g$ uniformly on compact subsets of $U$. If every $f_n$ is nowhere zero on $U$ and $g$ is not identically zero, then $g$ is nowhere zero on $U$: for every $z \in U$ we have $g(z) \neq 0$. Equivalently, a compact-open uniform limit of nowhere-vanishing holomorphic functions on a connected open set is either identically zero or nowhere vanishing.

import Mathlib
open Complex Finset Filter Topology

theorem hurwitz_nonvanishing_limit
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf_holo : ∀ n, AnalyticOnNhd ℂ (f n) U)
    (hf_nz : ∀ n, ∀ z ∈ U, f n z ≠ 0)
    (hconv : TendstoUniformlyOn f g atTop U)
    (hg_not_zero : ∃ z ∈ U, g z ≠ 0) :
    ∀ z ∈ U, g z ≠ 0 := by sorry
