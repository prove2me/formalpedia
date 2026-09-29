-- Prove2me | Theorems.Thm_mme_sum_inequality
-- name    : mme_sum_inequality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-30T19:08:44.526564+00:00
-- url     : https://prove2.me/theorems/27d594d9-b4e8-4ed7-9f57-ff39ebac8b27
-- statement:
--   **Schönhage's asymptotic sum inequality (general case, zero-dimension tolerant).**
--
--   For any finite family of matrix-multiplication tensor triples $(n_i, m_i, p_i)_{i=1}^k$ — with **no positivity assumption** on the dimensions:
--   $$\mathrm{tensorAsymptoticRank}\Bigl(\bigoplus_{i=1}^k \mathrm{MMObj}_K(n_i, m_i, p_i)\Bigr) \;\leq\; r \;\implies\; \sum_{i=1}^k (n_i m_i p_i)^{\omega/3} \;\leq\; r,$$
--   where $\omega = \mathrm{matMulExp\_strassen}\,K$.
--
--   This is the version actually used by the τ-theorem assembly (`mme_asymptotic_sum_inequality`): the user supplies a Schönhage-style direct-sum certificate without having to manually filter out degenerate dimensions, and the platform proves the inequality directly.
--
--   **Where it sits.** Direct child of the platform root `mme_asymptotic_sum_inequality` (Strassen's τ-theorem). Once proved, the τ-theorem is one `exact` away (`sketch_mme_asymptotic_sum_inequality`).
--
--   **Proof idea.** Reduce to the positive case (`mme_sum_inequality_pos`). Let $S = \{i : n_i, m_i, p_i \geq 1\}$ be the positive subfamily; reindex via an equivalence $e : \mathrm{Fin}\,|S| \simeq S$. On the **tensor side** the off-$S$ summands satisfy $\mathrm{MMq}_K(n_i,m_i,p_i) = 0$ (`mme_MMq_eq_zero_of_not_pos`), so the algebraic sum is unchanged; transport via `mme_bridge_asymptoticRank` (both directions) and the hypothesis $h$ carries over to the reindexed positive subfamily. On the **real side** the off-$S$ summands have $n_i m_i p_i = 0$ and $0^{\omega/3} = 0$ because $\omega/3 \neq 0$ (`mme_matMulExp_strassen_pos`). Apply `mme_sum_inequality_pos` on the reindexed family and rewrite back.
-- source:
--   https://github.com/EntropyIncreaser/Prism

import Definitions.Def_mme_tensor_bridge
open MME BigOperators
universe u

theorem mme_sum_inequality {K : Type u} [Field K] {k : ℕ} (n m p : Fin k → ℕ) (r : ℕ) (h : tensorAsymptoticRank (TensorObj.bigAdd (fun i => MMObj K (n i) (m i) (p i))) ≤ r) : ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ (matMulExp_strassen K / 3) ≤ r := by sorry
