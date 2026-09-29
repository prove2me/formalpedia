-- Prove2me | Theorems.Thm_mme_Ctensor_one_H_one_outer_family_cyclic_value_below
-- name    : mme_Ctensor_one_H_one_outer_family_cyclic_value_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T04:31:00.118809+00:00
-- url     : https://prove2.me/theorems/8a2701ae-e309-4aa2-a7e9-8b9476e01415
-- title:
--   Strict cyclic value bounds for a disjoint outer family of C-tensors
-- statement:
--   Let a tensor $T$ restrict to a modewise direct sum of $A$ C-tensors.  Each outer summand is a C-tensor over $\langle1,H,1\rangle$, and all of their component matrix products have common volume $v$, although their dimensions and fine-coordinate identifications may vary.  Fix $\tau$ with $3\tau\ge2$.  Then every nonnegative strict sub-bound
--
--   $$
--   0\le V<A^3H^2(v^3)^\tau
--   $$
--
--   is attained by the tau-value of the cyclic symmetrization of $T$.
--
--   The factor $A^3$ comes from the genuinely mode-disjoint triples of outer summands in $T\otimes\pi(T)\otimes\pi^2(T)$.  Within each heterogeneous triple, Strassen's balanced C-tensor argument gives the factor $H^2$ using only the common component volume.  No common fine tensor factor is assumed.
-- source:
--   V. Strassen's C-tensor value method as applied in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 271--272; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_tau_value

open MME

universe u

theorem mme_Ctensor_one_H_one_outer_family_cyclic_value_below
    {K : Type u} [Field K]
    {T : TensorObj K 3} {A H volume : ℕ}
    (stars : CTensorOneHOneFamilyCertificate T A H volume)
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < (A : ℝ) ^ 3 * (H : ℝ) ^ 2 *
        (((volume ^ 3 : ℕ) : ℝ) ^ tau)) :
    HasTauValueAtLeast (cyclicSymmetrization T) tau V := by
  sorry
