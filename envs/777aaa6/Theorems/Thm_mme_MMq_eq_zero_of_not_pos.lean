-- Prove2me | Theorems.Thm_mme_MMq_eq_zero_of_not_pos
-- name    : mme_MMq_eq_zero_of_not_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-30T19:07:15.434789+00:00
-- url     : https://prove2.me/theorems/1c7f4e5b-0086-497d-af97-760e668ede77
-- statement:
--   **Zero-dimension vanishing of the matrix-multiplication quotient element.**
--
--   If some dimension is zero ($\neg(1 \leq n \wedge 1 \leq m \wedge 1 \leq p)$), then $\mathrm{MMq}_K(n,m,p) = 0$ in the tensor quotient $\mathrm{TensorQ}\,K\,3$.
--
--   The underlying $\mathrm{MMObj}_K(n,m,p)$ is built from $\mathrm{MMTensor}\,n\,m\,p$, the explicit matrix-multiplication tensor $\sum_{i,j,k} e_{ij} \otimes e_{jk} \otimes e_{ki}$ in $(K^{n\times m}) \otimes (K^{m\times p}) \otimes (K^{p\times n})$. When any of $n, m, p$ is $0$, the sum is empty and the tensor is identically zero, so its quotient class — `MMq` — is the zero element of the `CommSemiring` structure on the quotient.
--
--   **Where it sits.** This is the structural fact powering the zero-dimension reduction in `mme_sum_inequality`. When index $i$ has some dimension zero, $\mathrm{MMq}_K(n_i,m_i,p_i) = 0$ drops out of the abstract sum without changing the asymptotic rank — which `mme_bridge_asymptoticRank` then transports to the concrete side.
-- source:
--   Definitional consequence of $\mathrm{MMTensor}$ vanishing when any index range is empty.

import Definitions.Def_mme_tensor_bridge
open MME
universe u

theorem mme_MMq_eq_zero_of_not_pos {K : Type u} [Field K] {n m p : ℕ} (h : ¬ (1 ≤ n ∧ 1 ≤ m ∧ 1 ≤ p)) : MMq K n m p = 0 := by sorry
