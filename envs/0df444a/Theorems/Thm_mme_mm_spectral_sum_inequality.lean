-- Prove2me | Theorems.Thm_mme_mm_spectral_sum_inequality
-- name    : mme_mm_spectral_sum_inequality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-30T19:06:20.906735+00:00
-- url     : https://prove2.me/theorems/8ec0e6aa-a840-4d37-bb26-27139358ad06
-- statement:
--   **The abstract asymptotic-spectrum sum inequality, instantiated at $\mathrm{mmTensorData}\,K$.**
--
--   For any finite family $(n_i, m_i, p_i)_{i=1}^k$ with all dimensions positive ($n_i, m_i, p_i \geq 1$), if
--   $$\mathrm{asymptoticRank}_{\mathrm{tensorPreorder}\,K}\Bigl(\textstyle\sum_i \mathrm{MMq}_K(n_i,m_i,p_i)\Bigr) \;\leq\; r,$$
--   then
--   $$\sum_{i=1}^k (n_i m_i p_i)^{\omega_{\mathrm{abs}}/3} \;\leq\; r,$$
--   where $\omega_{\mathrm{abs}} = (\mathrm{mmTensorData}\,K).\omega_{\mathrm{abs}}$ is the *abstract* (spectral) MM exponent.
--
--   This is the asymptotic-spectrum form of Schönhage's τ-inequality, **before** any identification of $\omega_{\mathrm{abs}}$ with the textbook Strassen-form $\omega$. It is the abstract theorem `MMData.sum_inequality` from `Def_mme_mm_spectral` applied to the bundle $\mathrm{mmTensorData}\,K$.
--
--   **Where it sits.** This is the spectral content of the τ-theorem on the abstract side. Combined with bridge A (`mme_bridge_asymptoticRank`, to translate the hypothesis into the concrete asymptotic rank) and bridge B (`mme_bridge_omega`, to replace $\omega_{\mathrm{abs}}$ by $\mathrm{matMulExp\_strassen}\,K$), it yields the concrete `mme_sum_inequality_pos`.
--
--   **Proof idea (in the abstract `MMData.sum_inequality`).** For every spectrum point $\varphi$:
--   1. $\varphi$ is a ring homomorphism plus monotone, so $\varphi\bigl(\sum_i \mathrm{MMq}(n_i,m_i,p_i)\bigr) = \sum_i \varphi(\mathrm{MMq}(n_i,m_i,p_i))$.
--   2. By the easy direction of Strassen duality, $\varphi \leq \mathrm{asymptoticRank} \leq r$ pointwise, so the sum of evaluations is $\leq r$.
--   3. The `MM_eval` API rewrites $\varphi(\mathrm{MMq}_K(n_i,m_i,p_i)) = n_i^{\theta_1} m_i^{\theta_2} p_i^{\theta_3}$ at $\varphi$.
--   4. AM–GM / Jensen on the triple $(\theta_1, \theta_2, \theta_3)$ (the abstract version of "$\omega \leq 3\theta_j$") collapses $n^{\theta_1} m^{\theta_2} p^{\theta_3}$ to $(nmp)^{(\theta_1+\theta_2+\theta_3)/3}$ at the maximizing point.
--   5. Taking $\sup_\varphi$ on the right-hand side picks up $\omega_{\mathrm{abs}}/3$ in the exponent.
-- source:
--   https://github.com/EntropyIncreaser/Prism

import Definitions.Def_mme_tensor_bridge
open MME BigOperators
universe u

theorem mme_mm_spectral_sum_inequality {K : Type u} [Field K] {k : ℕ} (n m p : Fin k → ℕ) (hn : ∀ i, 1 ≤ n i) (hm : ∀ i, 1 ≤ m i) (hp : ∀ i, 1 ≤ p i) (r : ℕ) (h : StrassenPreorder.asymptoticRank (tensorPreorder K) (∑ i, MMq K (n i) (m i) (p i)) ≤ r) : ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ ((mmTensorData K).omegaAbs / 3) ≤ r := by sorry
