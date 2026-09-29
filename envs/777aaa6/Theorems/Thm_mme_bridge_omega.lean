-- Prove2me | Theorems.Thm_mme_bridge_omega
-- name    : mme_bridge_omega
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-30T19:05:34.445087+00:00
-- url     : https://prove2.me/theorems/1eaaee8b-ace4-479d-8ba7-f56c3d00f23f
-- statement:
--   **Bridge B: the abstract spectral matrix-multiplication exponent equals the Strassen-form $\omega$.**
--
--   $$(\mathrm{mmTensorData}\,K).\omega_{\mathrm{abs}} \;=\; \mathrm{matMulExp\_strassen}\,K.$$
--
--   Here $(\mathrm{mmTensorData}\,K).\omega_{\mathrm{abs}}$ is the *abstract* MM exponent, defined as the supremum over the asymptotic spectrum
--   $$\omega_{\mathrm{abs}} \;=\; \sup_{\varphi \,\in\, \mathrm{AsymptoticSpectrumPoint}(\mathrm{TensorQ}\,K\,3,\, \mathrm{tensorPreorder}\,K)} \bigl(\theta_1(\varphi) + \theta_2(\varphi) + \theta_3(\varphi)\bigr),$$
--   where $\theta_j(\varphi) = \log_2 \varphi(\mathrm{MMq}_K(2,2,2))_j$ are the three "coordinate" exponents extracted by evaluating $\varphi$ on $\mathrm{MMq}_K$ via the `MM_eval` API. The right-hand side $\mathrm{matMulExp\_strassen}\,K$ is the Strassen-form exponent built textbook-style from `strassenRank`: $\mathrm{matMulExp\_strassen}\,K = \inf_n \log_n(\mathrm{strassenRank}(\mathrm{MMTensor}\,n\,n\,n))$.
--
--   This identity closes the loop: the *spectral* characterization of $\omega$ (as a supremum over the asymptotic spectrum) coincides with its *rank-growth* characterization (as the infimum of $\log_n$ of strassen ranks).
--
--   **Where it sits.** Cited by `mme_sum_inequality_pos` to rewrite the exponent in the conclusion from $\omega_{\mathrm{abs}}$ to $\mathrm{matMulExp\_strassen}\,K$.
--
--   **Proof idea.** Use compactness of the asymptotic spectrum (it is a closed subspace of a compact product of evaluation maps) and continuity of $\theta_1 + \theta_2 + \theta_3$ to pick a maximizing point $\varphi_\max$. At $\varphi_\max$ the evaluation of $\mathrm{MMq}_K(2,2,2)$ equals $2^{\theta_1+\theta_2+\theta_3}$ via `MM_eval`. Then Strassen duality (`mme_strassen_duality`) gives $\mathrm{asymptoticRank}(\mathrm{MMq}_K(2,2,2)) = 2^{\omega_{\mathrm{abs}}}$. Finally the canonical normalization $\mathrm{matMulExp\_strassen}\,K = \log_2 \mathrm{AR}(\mathrm{MMObj}_K(2,2,2))$ (from `Def_mme_omega_normalize`) closes the equality.
-- source:
--   https://github.com/EntropyIncreaser/Prism

import Definitions.Def_mme_tensor_bridge
open MME
universe u

theorem mme_bridge_omega {K : Type u} [Field K] : (mmTensorData K).omegaAbs = matMulExp_strassen K := by sorry
