-- Prove2me | Theorems.Thm_rademacher_paley_zygmund_meanzero_positivity
-- name    : rademacher_paley_zygmund_meanzero_positivity
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T05:02:43.74359+00:00
-- url     : https://prove2.me/theorems/c80210b8-45f0-4484-af5d-bc9466bf4849
-- statement:
--   de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211), **Proposition 1** (the real-valued Paley–Zygmund positivity step), stated on the **symmetric Rademacher ($\pm 1$) fiber** `rademacherExpectation` (the uniform $(1/2)^N$ measure on sign assignments).
--
--   For a mean-zero statistic $F$ ($\mathbb{E}F = 0$), the lower-tail probability $P(F \ge 0)$, expressed as the expectation of the indicator $\mathbf{1}_{\{F \ge 0\}}$ on the uniform sign measure, satisfies the product (division-free) Paley–Zygmund bound
--   $$ (\mathbb{E}|F|)^2 \le 4\,\mathbb{E}[F^2]\,\mathbb{E}[\mathbf{1}_{\{F \ge 0\}}], $$
--   equivalently $P(F \ge 0) \ge (\mathbb{E}|F|)^2/(4\,\mathbb{E}F^2)$.
--
--   Proof: mean-zero gives $\mathbb{E}|F| = 2\,\mathbb{E}[F\,\mathbf{1}_{\{F\ge 0\}}]$; then Cauchy–Schwarz with the indicator $g = \mathbf{1}_{\{F\ge 0\}}$ (using $g^2 = g$) gives $(\mathbb{E}[Fg])^2 \le \mathbb{E}[F^2]\,\mathbb{E}[g^2] = \mathbb{E}[F^2]\,\mathbb{E}[g]$, and $(\mathbb{E}|F|)^2 = 4(\mathbb{E}[Fg])^2$ finishes.
--
--   This is the Rademacher-fiber analogue of `bernoulli_paley_zygmund_meanzero_positivity`; the $\pm 1$ form is the classical lower-tail tool for symmetric sign chaos. Source: de la Peña–Montgomery-Smith 1995, Proposition 1; the Paley–Zygmund inequality (O'Donnell, *Analysis of Boolean Functions*, Ch. 9).

import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion
open scoped Classical BigOperators

theorem rademacher_paley_zygmund_meanzero_positivity
    {n₁ n₂ : ℕ}
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) :
    rademacherExpectation F = 0 →
    (rademacherExpectation (fun ε => |F ε|)) ^ 2 ≤
      4 * rademacherExpectation (fun ε => (F ε) ^ 2) *
        rademacherExpectation (fun ε => if 0 ≤ F ε then (1 : ℝ) else 0) := by sorry
