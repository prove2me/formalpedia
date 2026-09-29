-- Prove2me | Theorems.Thm_rademacher_sampled_matrix_schatten_moment_khintchine_q_ge_two_variance_scale
-- name    : rademacher_sampled_matrix_schatten_moment_khintchine_q_ge_two_variance_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-23T18:38:56.91332+00:00
-- url     : https://prove2.me/theorems/3090c7ef-8f8e-4ccd-96d5-e3f04aa44b9d
-- statement:
--   **Source-faithful $q\ge 2$ Khintchine-to-variance branch.**
--
--   Fix a sampled entry set $\Omega\subseteq [n_1]\times[n_2]$, a deterministic matrix $X\in\mathbb R^{n_1\times n_2}$, and $p=m/(n_1n_2)$. Let
--   $$
--   S_\varepsilon=p^{-1}\sum_{(i,j)\in\Omega}\varepsilon_{ij}X_{ij}e_ie_j^\top
--   $$
--   be the Rademacher-symmetrized sampled coordinate matrix.
--
--   This theorem asserts that there is a universal constant $C_{\mathrm{kh}}>0$ such that, for every larger constant $C'\ge C_{\mathrm{kh}}$, every $\beta>2$, and every integer $q\ge2$ satisfying $q\ge \beta\log(\max(n_1,n_2))$,
--   $$
--   \mathbb E_\varepsilon\,\lVert S_\varepsilon\rVert_{S_q}^{q}
--   \le
--   \bigl(C'\sqrt q\,\operatorname{varianceScale}(\Omega,p,X)\bigr)^q.
--   $$
--   This is the Candes-Recht Section 6.1, Lemma 6.1 noncommutative Khintchine estimate in the range where the source theorem actually applies, together with the diagonal Gram-to-variance comparison. The monotone-constant formulation is intentional: downstream reductions may enlarge $C'$ when combining this branch with a separate boundary case.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_gram_schatten
open MatrixCompletion

theorem rademacher_sampled_matrix_schatten_moment_khintchine_q_ge_two_variance_scale :
    ∃ Ckh : ℝ, 0 < Ckh ∧
      ∀ C' : ℝ, Ckh ≤ C' →
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
          (C' * Real.sqrt (q : ℝ) *
            rademacherSampledVarianceScale Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q := by
  sorry
