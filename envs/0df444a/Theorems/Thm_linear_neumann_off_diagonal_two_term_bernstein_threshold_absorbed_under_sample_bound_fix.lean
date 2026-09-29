-- Prove2me | Theorems.Thm_linear_neumann_off_diagonal_two_term_bernstein_threshold_absorbed_under_sample_bound_fix
-- name    : linear_neumann_off_diagonal_two_term_bernstein_threshold_absorbed_under_sample_bound_fix
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-25T02:09:21.471535+00:00
-- url     : https://prove2.me/theorems/6fca6d0c-9fd0-4e05-9c50-4056e7167be1
-- statement:
--   CR-faithful corrected off-diagonal first-Neumann two-term Bernstein threshold absorption. Same as the original leaf but with the $\mu_0$-linear sample lower bound $\max(\mu_0,\mu_1)$ (CR2009 Lemma 6.6 eq 6.15: $np\ge 4\beta\sqrt3\,\mu_0 r\log n$; Thm 1.3 eq 1.9 $\max(\mu_1^2,\mu_0\mu_1,\mu_0 n^{1/4})$), correcting the original's unsound $\max(\sqrt{\mu_0},\mu_1)$. The range term is $\mu_0$-linear, so only a $\mu_0$-linear sample bound absorbs the raw two-term Bernstein threshold $C_2(\sqrt{(\beta+2)\log n/p}\,F+((\beta+2)\log n/p)A)$ into the clean scale $C_{coef}\,\mu_1\sqrt{r/(n_1 n_2)}\sqrt{\mu_0 n r\beta\log n/m}$. Witness $C_{coef}=C_2(C_{fro}\sqrt2+2C_{entry})$.
-- source:
--   https://arxiv.org/abs/0805.4471 (Candes-Recht 2009) Lemma 6.6 eq 6.15; Thm 1.3 eq 1.9

import Definitions.Def_linear_neumann_offdiag_bernstein
open MatrixCompletion

theorem linear_neumann_off_diagonal_two_term_bernstein_threshold_absorbed_under_sample_bound_fix
    (Ctwo Centry Cfro : ℝ) :
    0 < Ctwo → 0 < Centry → 0 < Cfro →
    ∃ Ccoef : ℝ, 0 < Ccoef ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ μ₁ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max μ₀ μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        Ctwo *
            (Real.sqrt
                (((β + 2) * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Cfro * μ₁ *
                Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                  Real.sqrt (μ₀ * (r : ℝ) / (↑(max n₁ n₂)))) +
              (((β + 2) * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (Centry * μ₁ *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    (μ₀ * (r : ℝ) / (↑(max n₁ n₂))))) ≤
          Ccoef * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt
                ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                    (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)) := by
  sorry
