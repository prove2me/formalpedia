-- Prove2me | Theorems.Thm_mme_HasTauValueAtLeast_kronPow_root
-- name    : mme_HasTauValueAtLeast_kronPow_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T05:00:25.54981+00:00
-- url     : https://prove2.me/theorems/37afcf90-ce27-4f92-adfc-559e08a52e60
-- title:
--   Taking a positive Kronecker-power root of a tau-value bound
-- statement:
--   Let $T$ be an order-three tensor, let $r>0$, and let $V\ge0$. If the $r$-th Kronecker power of $T$ has tau-value at least $V^r$, then $T$ has tau-value at least $V$:
--
--   $$
--   V_\tau(T^{\otimes r})\ge V^r
--   \quad\Longrightarrow\quad
--   V_\tau(T)\ge V.
--   $$
--
--   The positive-exponent hypothesis is essential. The proof transports a cofinal sequence of witnesses for $(T^{\otimes r})^{\otimes s}$ to the powers $T^{\otimes rs}$, whose exponents remain cofinal, and uses the exact identity $(V^r)^s=V^{rs}$.
-- source:
--   Standard power law for Strassen's asymptotic tensor value, at the concrete witness level; D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), value definition and tensor-power arguments on journal pp. 264 and 270--272.

import Theorems.Thm_mme_HasTauValueAtLeast_to_cofinal_finite_extractions
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions
import Theorems.Thm_mme_kronPow_kronPow_isomorphic

open MME BigOperators Filter

universe u

theorem mme_HasTauValueAtLeast_kronPow_root
    {K : Type u} [Field K]
    (T : TensorObj K 3) (tau V : ℝ) (r : ℕ)
    (hr : 0 < r) (hV : 0 ≤ V)
    (hpower : HasTauValueAtLeast (T.kronPow r) tau (V ^ r)) :
    HasTauValueAtLeast T tau V := by
  sorry
