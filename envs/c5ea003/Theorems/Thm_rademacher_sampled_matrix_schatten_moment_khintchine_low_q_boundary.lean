-- Prove2me | Theorems.Thm_rademacher_sampled_matrix_schatten_moment_khintchine_low_q_boundary
-- name    : rademacher_sampled_matrix_schatten_moment_khintchine_low_q_boundary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-23T19:04:04.109482+00:00
-- url     : https://prove2.me/theorems/eb7d0058-f3d1-4621-bb77-569d35201005
-- statement:
--   **Low-$q$ boundary left after the source $q\ge2$ Khintchine range.**
--
--   The parent Khintchine node on Prove2Me is stated for integer $q$ with $1\le q$ and $q\ge\beta\log n$, where $n=\max(n_1,n_2)$ and $\beta>2$. Candes-Recht Section 6.1, Lemma 6.1, however, invokes the Lust-Picquard/Buchholz noncommutative Khintchine inequality only for $q\ge2$.
--
--   This theorem isolates exactly the remaining formal boundary case:
--   $$
--   1\le q,\qquad \neg(2\le q),\qquad q\ge\beta\log n.
--   $$
--   For natural-number $q$, this is the $q=1$ corner. In the paper-level applications, the lower bound $q\ge\beta\log n$ with $\beta>2$ forces $q\ge2$ whenever $n\ge2$; hence this theorem is a finite-dimensional/low-$q$ formal residue, not the analytic noncommutative Khintchine content. It is stated with a monotone constant $C_{\mathrm{big}}\ge C_{\mathrm{kh}}$ so it can be recombined cleanly with the source-faithful $q\ge2$ branch.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_gram_schatten
open MatrixCompletion

theorem rademacher_sampled_matrix_schatten_moment_khintchine_low_q_boundary :
    ∃ Ckh : ℝ, 0 < Ckh ∧
      ∀ Cbig : ℝ, Ckh ≤ Cbig →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ)
        (Omega : Finset (Fin n₁ × Fin n₂))
        (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        1 ≤ q →
        ¬ 2 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        rademacherExpectation
            (fun eps =>
              schattenNorm (q : ℝ)
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (Cbig * Real.sqrt (q : ℝ) *
            rademacherSampledVarianceScale Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q := by sorry
