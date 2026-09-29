-- Prove2me | Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
-- name    : mme_HasTauValueAtLeast_mono_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T05:00:21.112936+00:00
-- url     : https://prove2.me/theorems/cb0884f8-d1e0-4c3b-8c0e-6d179c23fc67
-- title:
--   Tau-value is monotone under tensor restriction
-- statement:
--   Let $X$ and $Y$ be order-three tensors over a field. If $X$ is a restriction of $Y$ and $X$ has tau-value at least $V$, then $Y$ has tau-value at least $V$:
--
--   $$
--   X\leq_{\mathrm{Restrict}}Y,\qquad V_\tau(X)\ge V
--   \quad\Longrightarrow\quad V_\tau(Y)\ge V.
--   $$
--
--   Indeed, every finite matrix-product extraction from a power of $X$ transports through the corresponding powered restriction from $Y$. The statement preserves the full witness-level definition of tau-value.
-- source:
--   Standard monotonicity of Strassen's tensor value under restriction; D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), value definition on journal p. 264.

import Definitions.Def_mme_tau_value
import Theorems.Thm_mme_restrict_kronPow

open MME BigOperators Filter

universe u

theorem mme_HasTauValueAtLeast_mono_restrict
    {K : Type u} [Field K]
    {X Y : TensorObj K 3} {tau V : ℝ}
    (hXY : TensorObj.Restrict X Y)
    (hX : HasTauValueAtLeast X tau V) :
    HasTauValueAtLeast Y tau V := by
  sorry
