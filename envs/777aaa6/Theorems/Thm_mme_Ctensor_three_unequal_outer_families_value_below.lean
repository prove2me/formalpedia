-- Prove2me | Theorems.Thm_mme_Ctensor_three_unequal_outer_families_value_below
-- name    : mme_Ctensor_three_unequal_outer_families_value_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T00:48:28.002086+00:00
-- url     : https://prove2.me/theorems/c1a0d5bf-44e7-4c30-bdc2-ff705968dd09
-- title:
--   Strict tau-value of the literal cyclic product of three unequal outer C-tensor families
-- statement:
--   For $i=0,1,2$, let $(S_{i,a})_{a=1}^{A_i}$ be a finite family of tensors over a field. Every member of family $i$ has an actual C-tensor certificate of shape $\langle1,H_i,1\rangle$ with one positive constant component volume $v_i$, where $H_i>0$.
--
--   Put $T_i=\bigoplus_{a=1}^{A_i}S_{i,a}$ and $\mu=\min(H_0H_1,H_0H_2,H_1H_2)$. For every real $\tau$ and every nonnegative $V$ satisfying
--   $$
--   V<A_0A_1A_2\,\mu\,(v_0v_1v_2)^\tau,
--   $$
--   the literal combined source has genuine asymptotic $\tau$-value at least $V$:
--   $$
--   V_\tau\bigl(T_0\otimes\operatorname{cyc}(T_1)\otimes\operatorname{cyc}^2(T_2)\bigr)\ge V.
--   $$
--
--   Outer counts, fiber counts, and component volumes may differ between the families. The conclusion retains the actual tensor source and the outer multiplicity; it assumes no tensor-value premise or identification of a whole shared-coordinate star with one matrix product. If an outer count is zero, no nonnegative $V$ satisfies the strict hypothesis.
-- source:
--   Finite unequal-family generalization of the existing Prove2Me theorem mme_Ctensor_outer_triple_distribution (8ad2742b-f657-4111-8997-7e79f5ce77e1), using its proved TensorQ finite direct-sum/Kronecker/permutation identities and converting the resulting equality back to actual tensor restriction. The asymptotic assembly reuses mme_HasTauValueAtLeast_bigAdd_uniform_strict (76941dd9-2fe8-4e25-980b-39360a4d913f), developed for the Stothers fourth-power mission, and restriction monotonicity, together with the genuine unequal three-star value-below theorem. This is a formal composition adapter, not claimed as a separately numbered paper theorem. It does not duplicate finite-power distribution or assume that independently frequent extraction powers intersect.

import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_threeStarCyclicProduct
import Definitions.Def_mme_tau_value

open MME

universe u

set_option autoImplicit false

theorem mme_Ctensor_three_unequal_outer_families_value_below
    {K : Type u} [Field K]
    {A0 A1 A2 H0 H1 H2 v0 v1 v2 : ℕ}
    (S0 : Fin A0 → TensorObj K 3)
    (S1 : Fin A1 → TensorObj K 3)
    (S2 : Fin A2 → TensorObj K 3)
    (cert0 : ∀ a, CTensorOneHOneCertificate (S0 a) H0 v0)
    (cert1 : ∀ a, CTensorOneHOneCertificate (S1 a) H1 v1)
    (cert2 : ∀ a, CTensorOneHOneCertificate (S2 a) H2 v2)
    (h0 : 0 < H0) (h1 : 0 < H1) (h2 : 0 < H2)
    (hv0 : 0 < v0) (hv1 : 0 < v1) (hv2 : 0 < v2)
    (tau V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < ((A0 * A1 * A2 : ℕ) : ℝ) *
      ((min (H0 * H1) (min (H0 * H2) (H1 * H2)) : ℕ) : ℝ) *
      (((v0 * v1 * v2 : ℕ) : ℝ) ^ tau)) :
    HasTauValueAtLeast
      (threeStarCyclicProduct
        (TensorObj.bigAdd S0) (TensorObj.bigAdd S1) (TensorObj.bigAdd S2)) tau V := by sorry
