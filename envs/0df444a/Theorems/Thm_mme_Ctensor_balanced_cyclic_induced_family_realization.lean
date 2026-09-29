-- Prove2me | Theorems.Thm_mme_Ctensor_balanced_cyclic_induced_family_realization
-- name    : mme_Ctensor_balanced_cyclic_induced_family_realization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T02:47:49.937097+00:00
-- url     : https://prove2.me/theorems/5d272dc4-96e5-4572-9882-63dac6d01fde
-- title:
--   An induced family of balanced C-tensor blocks gives a direct-sum restriction
-- statement:
--   Let $T$ have a C-tensor certificate over $\langle 1,H,1\rangle$ with all $H>0$ components of common volume $v$. Put $R=Hm$, and index the balanced length-$R$ component words by a set of size $W$. Suppose $E\subseteq[W]^3$ is an induced family: its three pair projections are injective, and no mixed triple assembled from three edges lies in the support unless all three edges coincide. Then
--
--   $$
--   (T\otimes\pi T\otimes\pi^2T)^{\otimes R}
--   \;\ge\;\bigoplus_{e\in E}\langle a_e,b_e,c_e\rangle,
--   \qquad a_eb_ec_e=v^{3R}.
--   $$
--
--   This is the finite tensor-coordinate core of Strassen's C-tensor argument. It contains no density estimate: the induced family is supplied explicitly. Pair-projection injectivity gives mode disjointness, while the mixed-edge condition makes coordinate zeroing induced. Component identifications are performed only after this pruning, so the statement does not assume a false common fine factorization along the shared C-tensor mode.
-- source:
--   V. Strassen's C-tensor value method and the Salem--Spencer pruning step as used in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 271--272; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_tensor_rank

open MME BigOperators

universe u

theorem mme_Ctensor_balanced_cyclic_induced_family_realization
    {K : Type u} [Field K]
    {T : TensorObj K 3} {H volume : ℕ}
    (cert : CTensorOneHOneCertificate T H volume)
    (hH : 0 < H) (m : ℕ) :
    let R : ℕ := H * m
    let W : ℕ :=
      Nat.card
        {w : Fin R → Fin H // ∀ h,
          Fintype.card {j // w j = h} = m}
    ∀ (E : Finset (Fin W × Fin W × Fin W)),
      Function.Injective
          (fun e : E ↦ (e.1.1, e.1.2.1)) →
      Function.Injective
          (fun e : E ↦ (e.1.2.1, e.1.2.2)) →
      Function.Injective
          (fun e : E ↦ (e.1.2.2, e.1.1)) →
      (∀ x y z : E,
        x.1.2.1 = y.1.2.1 →
        y.1.2.2 = z.1.2.2 →
        z.1.1 = x.1.1 →
        x = y ∧ y = z) →
      ∃ (a b c : Fin E.card → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
          ((cyclicSymmetrization T).kronPow R) ∧
        (∀ i, a i * b i * c i = volume ^ (3 * R)) := by
  sorry
