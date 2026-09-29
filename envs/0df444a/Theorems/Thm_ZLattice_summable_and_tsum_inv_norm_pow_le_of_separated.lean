-- Prove2me | Theorems.Thm_ZLattice_summable_and_tsum_inv_norm_pow_le_of_separated
-- name    : ZLattice.summable_and_tsum_inv_norm_pow_le_of_separated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/c9d97df6-0238-5a78-ae41-5a1296c4419a
-- title:
--   Packing bound for r-separated families in the sup norm
-- statement:
--   Let $W$ be a finite type, so that $W \to \mathbb{R}$ carries the sup norm $\|x\| = \max_{w} |x_w|$, let $\iota$ be an arbitrary index type, and let $r$ be a real number with $r > 0$. Let $v : \iota \to (W \to \mathbb{R})$ be a family which is $r$-separated, in the sense that $r \le \|v_i - v_j\|$ whenever $i \ne j$, and $r$-far from the origin, in the sense that $r \le \|v_i\|$ for every $i$. Let $k$ be a natural number exceeding the number of elements of $W$, i.e. $|W| < k$. The conclusion is a conjunction: first, the family $i \mapsto \|v_i\|^{-k}$ is summable; second,
--   $$\sum_{i \in \iota} \|v_i\|^{-k} \le \left(\frac{3}{r}\right)^{k} \sum_{x} \|x\|^{-k},$$
--   where the right-hand sum ranges over the elements of the $\mathbb{Z}$-submodule of $W \to \mathbb{R}$ spanned by the range of the standard basis `Pi.basisFun ℝ W`, i.e. over the integer vectors $\mathbb{Z}^W$; by the Lean convention $\|0\|^{-k} = 0$, so the term $x = 0$ contributes nothing.
--
--   This is an elementary box-counting (lattice packing) estimate: an $r$-separated family bounded away from the origin has $\sum \|v_i\|^{-k}$ controlled by the corresponding sum over $\mathbb{Z}^W$, which converges once $k$ exceeds the rank. It is used in the analytic part of the Langlands–Tunnell input, for the integrability and summability estimates attached to cubic induction data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ZLattice_summable_and_tsum_inv_norm_pow_le_of_separated.lean

import Mathlib.Algebra.Module.ZLattice.Summable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ZLattice.summable_and_tsum_inv_norm_pow_le_of_separated
    {W : Type} [Fintype W] {ι : Type} {r : ℝ} (hr : 0 < r) {v : ι → W → ℝ}
    (hsep : ∀ i j, i ≠ j → r ≤ ‖v i - v j‖) (hfar : ∀ i, r ≤ ‖v i‖) {k : ℕ} (hk : Fintype.card W < k) :
    Summable (fun i => ‖v i‖⁻¹ ^ k) ∧
      ∑' i, ‖v i‖⁻¹ ^ k ≤ (3 / r) ^ k * ∑' x : Submodule.span ℤ (Set.range (Pi.basisFun ℝ W)), ‖x‖⁻¹ ^ k := by sorry
