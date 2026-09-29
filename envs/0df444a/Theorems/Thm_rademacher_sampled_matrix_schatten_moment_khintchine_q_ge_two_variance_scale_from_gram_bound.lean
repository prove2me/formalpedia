-- Prove2me | Theorems.Thm_rademacher_sampled_matrix_schatten_moment_khintchine_q_ge_two_variance_scale_from_gram_bound
-- name    : rademacher_sampled_matrix_schatten_moment_khintchine_q_ge_two_variance_scale_from_gram_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-23T20:36:37.254532+00:00
-- url     : https://prove2.me/theorems/df2ab974-47ba-4fc5-bee8-927c7f29d8f2
-- statement:
--   **Formal recombination lemma for the $q\ge 2$ Khintchine branch.**
--
--   Let $\Omega\subseteq [n_1]\times[n_2]$ be a fixed observation set, let $X\in\mathbb{R}^{n_1\times n_2}$, set
--   $$
--   p={m\over n_1n_2},\qquad n=\max\{n_1,n_2\},
--   $$
--   and write $S_\varepsilon(\Omega,p,X)$ for the Rademacher-signed sampled matrix. This theorem is the purely formal step that turns a diagonal-Gram noncommutative Khintchine estimate into the variance-scale estimate used by Candes--Recht.
--
--   The two analytic inputs assumed by this node are:
--   $$
--   \mathbb{E}_\varepsilon\,\|S_\varepsilon(\Omega,p,X)\|_{S_q}^q
--   \le
--   \left(C_{\rm core}\sqrt q\,\max\{G_{\rm row}(\Omega,p,X,q),G_{\rm col}(\Omega,p,X,q)\}\right)^q,
--   $$
--   and, in the range $q\ge \beta\log n$,
--   $$
--   \max\{G_{\rm row}(\Omega,p,X,q),G_{\rm col}(\Omega,p,X,q)\}
--   \le e^{1/2} V(\Omega,p,X),
--   $$
--   where $V$ is `rademacherSampledVarianceScale`. The conclusion is that there is a universal constant $C_{\rm Kh}>0$ such that every larger constant $C_{\rm big}\ge C_{\rm Kh}$ satisfies
--   $$
--   \mathbb{E}_\varepsilon\,\|S_\varepsilon(\Omega,p,X)\|_{S_q}^q
--   \le
--   \left(C_{\rm big}\sqrt q\,V(\Omega,p,X)\right)^q.
--   $$
--
--   Thus the node contains no new probability estimate: it only absorbs the fixed factor $e^{1/2}$ and preserves the monotone-universal-constant interface.
--
--   Source: Candes--Recht, Section 6.1, Lemma 6.1, PDF p. 24, plus the row/column Gram-to-variance comparison immediately following that lemma. This node is the Lean bridge that recombines those source-backed estimates.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_gram_schatten
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open MatrixCompletion

theorem rademacher_sampled_matrix_schatten_moment_khintchine_q_ge_two_variance_scale_from_gram_bound
    (Ccore : ℝ) :
    0 < Ccore →
    (∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ)
        (Omega : Finset (Fin n₁ × Fin n₂))
        (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        2 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        rademacherExpectation
            (fun eps =>
              schattenNorm (q : ℝ)
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (Ccore * Real.sqrt (q : ℝ) *
            max (sampledRowGramSchatten Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X (q : ℝ))
                (sampledColumnGramSchatten Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X (q : ℝ))) ^ q) →
    (∀ {n₁ n₂ : ℕ}
        (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ)
        (X : Matrix (Fin n₁) (Fin n₂) ℝ)
        (q β : ℝ), 0 ≤ p → 2 < β → 1 ≤ q →
        q ≥ β * Real.log (↑(max n₁ n₂)) →
        max (sampledRowGramSchatten Omega p X q)
            (sampledColumnGramSchatten Omega p X q) ≤
          Real.exp (1 / 2) * rademacherSampledVarianceScale Omega p X) →
    ∃ Ckh : ℝ, 0 < Ckh ∧
      ∀ Cbig : ℝ, Ckh ≤ Cbig →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ)
        (Omega : Finset (Fin n₁ × Fin n₂))
        (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        2 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        rademacherExpectation
            (fun eps =>
              schattenNorm (q : ℝ)
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (Cbig * Real.sqrt (q : ℝ) *
            rademacherSampledVarianceScale Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q := by
  sorry
