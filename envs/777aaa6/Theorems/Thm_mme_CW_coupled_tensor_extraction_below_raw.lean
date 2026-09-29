-- Prove2me | Theorems.Thm_mme_CW_coupled_tensor_extraction_below_raw
-- name    : mme_CW_coupled_tensor_extraction_below_raw
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-07T14:47:40.866337+00:00
-- url     : https://prove2.me/theorems/9347194b-c614-44bd-8237-6fda16baecc4
-- title:
--   Even-power extraction from the coupled constituent at every q
-- statement:
--   Finite extraction from even powers of the coupled constituent, at every $q\ge3$.
--
--   Let $q\ge3$, $3\tau\ge2$, and let $0\le V<\mathrm{raw}=4q^{3\tau}(q^{3\tau}+2)$. Then eventually in $N$, on the floor profile satisfying the pruning conditions, the $2N$-th Kronecker power of the cyclic symmetrisation of the coupled constituent restricts from a direct sum of $k$ matrix-multiplication tensors with
--   $$V^{2N}\;\le\;\sum_i (a_ib_ic_i)^{\tau}.$$
--
--   The proof multiplies three ingredients: the capacity estimate `mme_CW_primary_profile_capacity_quarter_root`, the hash certificates `mme_CW_primary_hash_Ctensor_outer_middle_certificates`, and the quarter-root absorption `mme_MM_induced_matching_quarter_root_absorption` that converts the Behrend loss $e^{-100\sqrt{\log H}}$ into the uniform quarter-root loss. Every surviving star contributes the same volume $\bigl(q^{4G+2L}\bigr)^3$, so the weighted sum collapses to $k\cdot(\text{side}^3)^\tau$ and the estimate becomes the capacity inequality.
--
--   The strict inequality $V<\mathrm{raw}$ is what makes the argument work: it gives $V\le \mathrm{raw}\cdot e^{-\text{loss}}$ for all large $N$, and the two factors of $e^{-N\,\text{loss}}$ that this produces are exactly what pay for the hashing and Behrend losses.
--
--   General-$q$ form of `mme_CW_q6_coupled_tensor_extraction_below_raw_of_pruning`, with the pruning conditions supplied as a hypothesis.
-- source:
--   Don Coppersmith and Shmuel Winograd, Matrix multiplication via arithmetic progressions, Journal of Symbolic Computation 9(3), 1990, 251-280; the coupled four-sum constituent (d) on printed p. 266 and its value lemma on printed p. 270. General-q form of the q=6 chain used for omega < 2.376.

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_mme_CW_coupled_value
open MME BigOperators Filter
universe u

theorem mme_CW_coupled_tensor_extraction_below_raw
    {K : Type u} [Field K] (q : ℕ) (hq : 3 ≤ q)
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < 4 * (q : ℝ) ^ (3 * tau) *
        ((q : ℝ) ^ (3 * tau) + 2)) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((q : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let G : ℕ := N - L
      (0 < L ∧ 0 < G ∧ L + G = N ∧ 341 * L < 100 * G) →
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
          ((cyclicSymmetrization (coupledObj K q)).kronPow (2 * N)) ∧
        V ^ (2 * N) ≤
          ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  sorry
