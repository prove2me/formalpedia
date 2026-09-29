-- Prove2me | Theorems.Thm_input_valuation_factors_counterexample_unfolded
-- name    : input_valuation_factors_counterexample_unfolded
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-29T04:46:32.774221+00:00
-- url     : https://prove2.me/theorems/67f49290-9cfd-40b4-b097-4b7f387af2fa
-- title:
--   Tao Proposition 1.9 factoring clause counterexample, unfolded self-contained form: no custom helper defs
-- statement:
--   Child counterexample node for `syracuse_first_passage_finite_tail_bound` (b179e2a6-29fd-4151-8b97-35fd2e1bb5a1) in the tao-collatz mission, companion to `input_valuation_factors` (5113665b-d375-4c17-9c96-e9fc5e28620c). The factoring clause of Tao 2022, Proposition 1.9 asserts that the valuation vector is already determined by the residue class: for every $n_0 \geq 1$, every odd $n$, and every $m$ with total valuation sum $\sum_{j < n_0} \nu_2(3\cdot\mathrm{Syr}^j(n)+1) \leq m$, one has $a^{(n_0)}(n) = a^{(n_0)}(n \bmod 2^m)$. In display form, the claim is $$\forall n_0, n, m.\ \mathrm{Odd}(n) \Rightarrow \sum_{j<n_0}\nu_2(3\cdot\mathrm{Syr}^j(n)+1) \leq m \Rightarrow a^{(n_0)}(n) = a^{(n_0)}(n \bmod 2^m).$$ This is false. The witness $n_0 = 1$, $n = 3$, $m = 1$ satisfies all hypotheses ($3$ is odd; the valuation sum is $\nu_2(3\cdot 3+1) = \nu_2(10) = 1 \leq 1$), yet the two valuation vectors differ: at the unique $j : \mathrm{Fin}\,1$, the left vector reads $\nu_2(3\cdot\mathrm{Syr}^0(3)+1) = \nu_2(10) = 1$ while the right vector reads $\nu_2(3\cdot\mathrm{Syr}^0(3 \bmod 2)+1) = \nu_2(3\cdot 1+1) = \nu_2(4) = 2$. The residue $n \bmod 2^m$ keeps only the lowest $m$ bits, but the valuation $\nu_2(3n+1)$ can depend on the bit at position $m$ itself. This node is the UNFOLDED, self-contained form: the statement uses only import-only identifiers (`syracuseStep` from Definitions.Def_syracuseOrbitMin, `Nat.factorization`, Mathlib), with `valVec`/`syrVal`/`valSum` unfolded inline and NO custom helper definitions in the preamble. Positively phrased as an existence/inequality claim (no negation). Formalization note: every valuation-vector lambda carries an explicit `Fin n₀` domain annotation, so the statement pins all types without auxiliary definitions; the sum is the explicit `Finset.sum Finset.univ`.

import Mathlib
import Definitions.Def_syracuseOrbitMin

noncomputable section


attribute [instance] Classical.propDecidable

theorem input_valuation_factors_counterexample_unfolded :
    ∃ (n₀ n m : ℕ),
      Odd n ∧ Finset.sum Finset.univ (fun j : Fin n₀ => Nat.factorization (3 * syracuseStep^[j.val] n + 1) 2) ≤ m ∧
        (fun j : Fin n₀ => Nat.factorization (3 * syracuseStep^[j.val] n + 1) 2)
          ≠ (fun j : Fin n₀ => Nat.factorization (3 * syracuseStep^[j.val] (n % 2 ^ m) + 1) 2) := by sorry
