-- Prove2me | Theorems.Thm_mme_bridge_asymptoticRank
-- name    : mme_bridge_asymptoticRank
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-30T19:04:47.068006+00:00
-- url     : https://prove2.me/theorems/d1858151-01ba-4a71-b4b5-08a28ec61753
-- statement:
--   **Bridge A: abstract spectrum asymptotic rank equals concrete tensor asymptotic rank for matrix-multiplication direct sums.**
--
--   For any finite family of triples $(n_i, m_i, p_i)_{i=1}^k$ of natural-number dimensions,
--   $$\mathrm{asymptoticRank}_{\mathrm{tensorPreorder}\,K}\Bigl(\textstyle\sum_i \mathrm{MMq}_K(n_i, m_i, p_i)\Bigr) \;=\; \mathrm{tensorAsymptoticRank}\Bigl(\bigoplus_{i=1}^k \mathrm{MMObj}_K(n_i, m_i, p_i)\Bigr).$$
--
--   The left-hand side is the abstract asymptotic rank in the canonical Strassen preorder on the **tensor quotient** $\mathrm{TensorQ}\,K\,3$ — the quotient of 3-mode tensors by isomorphism, equipped with the asymptotic-restriction order — applied to the algebraic sum (in the quotient `CommSemiring`) of the matrix-multiplication classes $\mathrm{MMq}_K(n_i,m_i,p_i)$. The right-hand side is the concrete `tensorAsymptoticRank` defined directly on `TensorObj` via subexponential growth of the explicit `tensorRankObj`, applied to the **direct sum** $\bigoplus_i \mathrm{MMObj}_K(n_i, m_i, p_i)$.
--
--   This identity is what lets the asymptotic-spectrum machinery (developed abstractly over the tensor quotient) speak about concrete matrix-multiplication tensors. It is one of the two structural "bridges" in the τ-theorem decomposition; the other is `mme_bridge_omega`.
--
--   **Where it sits.** In the τ-theorem branch of the MME ω<51/20 program, this leaf is cited by `mme_sum_inequality_pos` (positive case of Schönhage's asymptotic sum inequality) and by `mme_sum_inequality` (the general case, via the zero-dimension reduction).
--
--   **Proof idea.** Both sides reduce to the same `iInf`: the canonical Strassen preorder on `TensorQ` has `le` defeq to `TensorQ.le`, so `tensorPreorder K = TensorQ.tensorStrassen K 3` (by `StrassenPreorder.ext`). Then `TensorQ.tensorAsymptoticRank_eq` translates the abstract asymptotic rank into the concrete one, and `TensorQ.toQ_bigAdd` matches the algebraic sum of `MMq`s with the quotient class of the direct sum of `MMObj`s. The conclusion is `rfl`.
-- source:
--   https://github.com/EntropyIncreaser/Prism

import Definitions.Def_mme_tensor_bridge
open MME BigOperators
universe u

theorem mme_bridge_asymptoticRank {K : Type u} [Field K] {k : ℕ} (n m p : Fin k → ℕ) : StrassenPreorder.asymptoticRank (tensorPreorder K) (∑ i, MMq K (n i) (m i) (p i)) = tensorAsymptoticRank (TensorObj.bigAdd (fun i => MMObj K (n i) (m i) (p i))) := by sorry
