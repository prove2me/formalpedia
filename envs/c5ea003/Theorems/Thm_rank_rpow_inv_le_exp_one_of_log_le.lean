-- Prove2me | Theorems.Thm_rank_rpow_inv_le_exp_one_of_log_le
-- name    : rank_rpow_inv_le_exp_one_of_log_le
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-06-23T21:37:34.510622+00:00
-- url     : https://prove2.me/theorems/c559deb6-2645-4d41-a971-ed83799804ef
-- statement:
--   Window-collapse bridge (b) for the noncommutative matrix-Khintchine general-$q$ pipeline. For a natural number $N \ge 1$ (the matrix rank) and a real exponent $q \ge 1$ with $\log N \le q$, one has $N^{1/q} \le e$. This is the elementary estimate behind CR2009 §6.1's operator-norm/Schatten sandwich $\lVert X\rVert \le \lVert X\rVert_{S_q} \le e\lVert X\rVert$ valid for $q \ge \log n$: combined with $\lVert X\rVert_{S_q} \le \operatorname{rank}(X)^{1/q}\,\lVert X\rVert$ (node F6), it collapses the rank prefactor to the absolute constant $e$. Proof: $N^{1/q} = \exp(q^{-1}\log N)$ and $q^{-1}\log N \le 1$ since $0 \le \log N \le q$.
-- source:
--   Candès & Recht, Exact Matrix Completion via Convex Optimization (arXiv:0805.4471), §6.1, the operator-norm/Schatten-q sandwich estimate (the bound rank^{1/q} ≤ e for q ≥ log rank).

import Mathlib
open scoped Real

theorem rank_rpow_inv_le_exp_one_of_log_le
    (N : ℕ) (q : ℝ) (hN : 1 ≤ N) (hq : 1 ≤ q)
    (hlog : Real.log (N : ℝ) ≤ q) :
    Real.rpow (N : ℝ) q⁻¹ ≤ Real.exp 1 := by sorry
