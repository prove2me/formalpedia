-- Prove2me | Theorems.Thm_mme_paired_Ctensor_certificate_to_six_symmetric_tau_value
-- name    : mme_paired_Ctensor_certificate_to_six_symmetric_tau_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T10:38:41.013416+00:00
-- url     : https://prove2.me/theorems/1e969e7d-1961-4a44-96b4-c26d74174cfc
-- title:
--   Paired C-tensor families yield six-symmetrized tau value
-- statement:
--   Let $T$ be any trilinear tensor. Suppose the literal paired tensor $T \otimes \operatorname{swap}_{12}(T)$ has an outer family of $A$ C-tensor stars, each with $H$ matrix-multiplication components, such that every component has the same volume $m_h n_h p_h=v$. Then, for $3\tau\ge 2$, the six-symmetrization of $T$ has $\tau$-value at least every nonnegative real $V$ satisfying
--
--   $$V<A^3H^2(v^3)^\tau.$$
--
--   The component shapes may vary; only their common volume is used. The proof cyclically balances the three paired stars and transports the resulting restriction through the canonical isomorphism between the six-symmetrization of $T$ and the cyclic symmetrization of $T\otimes\operatorname{swap}_{12}(T)$.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Sections 5-6, especially the C-tensor value analysis in Section 6.3; Volker Strassen, Relative Bilinear Complexity and Matrix Multiplication, 1987, cyclic value method.

import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_six_symmetrized_tau_value

open MME

universe u

set_option autoImplicit false

theorem mme_paired_Ctensor_certificate_to_six_symmetric_tau_value
    {K : Type u} [Field K]
    {T : TensorObj K 3} {A H volume : ℕ}
    (stars : CTensorOneHOneFamilyCertificate
      (TensorObj.kron T (TensorObj.permObj swapFirstTwoPerm T))
      A H volume)
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < (A : ℝ) ^ 3 * (H : ℝ) ^ 2 *
      (((volume ^ 3 : ℕ) : ℝ) ^ tau)) :
    HasTauValueAtLeast (sixSymmetrization T) tau V := by
  sorry
