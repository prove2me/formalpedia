-- Prove2me | Theorems.Thm_mme_sum_inequality_pos
-- name    : mme_sum_inequality_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-30T19:07:59.804276+00:00
-- url     : https://prove2.me/theorems/bf93e58c-6e77-4126-8f23-8bc3c70fd9a7
-- statement:
--   **Schönhage's asymptotic sum inequality (positive case).**
--
--   For any finite family of matrix-multiplication tensor triples $(n_i, m_i, p_i)_{i=1}^k$ with all dimensions positive ($n_i, m_i, p_i \geq 1$):
--   $$\mathrm{tensorAsymptoticRank}\Bigl(\bigoplus_{i=1}^k \mathrm{MMObj}_K(n_i, m_i, p_i)\Bigr) \;\leq\; r \;\implies\; \sum_{i=1}^k (n_i m_i p_i)^{\omega/3} \;\leq\; r,$$
--   where $\omega = \mathrm{matMulExp\_strassen}\,K$ is the Strassen-form matrix-multiplication exponent.
--
--   This is the **all-positive** form of Strassen's τ-theorem (a.k.a. Schönhage's asymptotic sum inequality), one of the central tools in the modern theory of fast matrix multiplication: it lets you trade an upper bound on the asymptotic rank of a *direct sum* of MM-tensors for an inequality among the individual sizes, weighted by $\omega/3$ in the exponent. Schönhage used it to derive $\omega \leq 51/20 = 2.55$ from the direct-sum identity for $\langle 4,1,4\rangle \oplus \langle 1,9,1\rangle$.
--
--   **Where it sits.** Direct child of the general `mme_sum_inequality` (which adds zero-dimension tolerance). It is itself reduced to the abstract spectral sum inequality (`mme_mm_spectral_sum_inequality`) plus the two bridges A and B (`mme_bridge_asymptoticRank`, `mme_bridge_omega`).
--
--   **Proof idea.** Translate the hypothesis to the abstract asymptotic rank via bridge A; apply the abstract sum inequality at $\mathrm{mmTensorData}\,K$; rewrite $\omega_{\mathrm{abs}}$ to $\mathrm{matMulExp\_strassen}\,K$ via bridge B.
-- source:
--   https://github.com/EntropyIncreaser/Prism

import Definitions.Def_mme_tensor_bridge
open MME BigOperators
universe u

theorem mme_sum_inequality_pos {K : Type u} [Field K] {k : ℕ} (n m p : Fin k → ℕ) (hn : ∀ i, 1 ≤ n i) (hm : ∀ i, 1 ≤ m i) (hp : ∀ i, 1 ≤ p i) (r : ℕ) (h : tensorAsymptoticRank (TensorObj.bigAdd (fun i => MMObj K (n i) (m i) (p i))) ≤ r) : ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ (matMulExp_strassen K / 3) ≤ r := by sorry
