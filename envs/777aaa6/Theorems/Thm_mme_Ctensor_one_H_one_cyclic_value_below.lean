-- Prove2me | Theorems.Thm_mme_Ctensor_one_H_one_cyclic_value_below
-- name    : mme_Ctensor_one_H_one_cyclic_value_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T01:53:34.308383+00:00
-- url     : https://prove2.me/theorems/f9b5bbdf-5ed3-4b90-993d-1fbf74989677
-- title:
--   Strict cyclic value bounds for a C-tensor over $\langle1,H,1\rangle$
-- statement:
--   Let $T$ be a C-tensor over $\langle1,H,1\rangle$. Its $H$ supported components share one third-mode grade, are disjoint in the first two mode grades, and the $h$-th component is a matrix-multiplication tensor $\langle m_h,n_h,p_h\rangle$. Assume that all component volumes equal $v$:
--
--   $$
--   m_hn_hp_h=v.
--   $$
--
--   Fix $\tau$ with $3\tau\ge2$. Then every nonnegative strict sub-bound
--
--   $$
--   0\le V<H^2(v^3)^\tau
--   $$
--
--   is attained by the witness-level tau-value of the cyclic symmetrization $T\otimes\pi(T)\otimes\pi^2(T)$.
--
--   The strict inequality is intentional. Balanced type classes and induced-matching extraction incur subexponential losses, which establish the asymptotic base $H^2(v^3)^\tau$ but do not generally give a constant relative factor at the exact endpoint in the platform's witness predicate. This is the source-faithful C-tensor value step used on Coppersmith--Winograd journal pp. 271--272.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 271--272: C-tensor over <1,H,1>, component class m*n*p=q^(4G+2L), and the ensuing asymptotic value estimate; https://doi.org/10.1016/S0747-7171(08)80013-2. The C-tensor machinery is attributed there to V. Strassen.

import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_mme_tau_value
import Definitions.Def_mme_CW_coupled_value

open MME Filter

universe u

theorem mme_Ctensor_one_H_one_cyclic_value_below
    {K : Type u} [Field K]
    {T : TensorObj K 3} {H volume : ℕ}
    (cert : CTensorOneHOneCertificate T H volume)
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < (H : ℝ) ^ 2 * (((volume ^ 3 : ℕ) : ℝ) ^ tau)) :
    HasTauValueAtLeast (cyclicSymmetrization T) tau V := by
  sorry
