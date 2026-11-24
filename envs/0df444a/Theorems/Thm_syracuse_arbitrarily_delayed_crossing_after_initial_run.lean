-- Prove2me | Theorems.Thm_syracuse_arbitrarily_delayed_crossing_after_initial_run
-- name    : syracuse_arbitrarily_delayed_crossing_after_initial_run
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T12:36:44.935793+00:00
-- url     : https://prove2.me/theorems/dcf85dea-8b24-4005-8c44-2c3b8830355f
-- title:
--   An arbitrarily long strict decrease above the original Syracuse starting value
-- statement:
--   For each $k\ge6$ there is one residue $r$ modulo $P=4^{2k+1}$ specified by $3^{k-1}r\equiv1\pmod P$. For every positive $q\equiv r\pmod P$ put $n=2^kq-1$ and $y=\operatorname{oddpart}(3^kq-1)$. The first $2k$ Syracuse steps from $y$ are strictly decreasing. All iterates at indices $0,\ldots,k$ stay strictly above $n$, while the iterate at index $2k$ is strictly below $n$. Since $y$ is the $k$th odd iterate of $n$ and all earlier positive iterates exceed $n$, the first descent from $n$ occurs between odd steps $2k+1$ and $3k$, inclusive. The post-ascent delay is unbounded even on these explicitly descending progressions.
-- source:
--   Uses syracuse_exact_contraction_block and the previously verified initial-run interpretation https://prove2.me/theorems/cd5cee3d-2614-45b1-abbd-326d3f73988d. Applies within https://prove2.me/theorems/2608ffdc-2f1d-4f5a-bf8d-7c3af9948d46.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

open Nat

theorem syracuse_arbitrarily_delayed_crossing_after_initial_run (k : ℕ) (hk : 6 ≤ k) :
    ∃ r < 4^(2*k+1),
      (∀ q : ℕ, (3^(k-1)*q) % 4^(2*k+1) = 1 ↔ q % 4^(2*k+1) = r) ∧
      ∀ q : ℕ, 0 < q → q % 4^(2*k+1) = r →
        let n := 2^k*q-1
        let y := ordCompl[2] (3^k*q-1)
        (∀ j : ℕ, j ≤ k → n < syracuseStep^[j] y) ∧
        syracuseStep^[2*k] y < n ∧
        (∀ j : ℕ, j < 2*k → syracuseStep^[j+1] y < syracuseStep^[j] y) := by sorry
