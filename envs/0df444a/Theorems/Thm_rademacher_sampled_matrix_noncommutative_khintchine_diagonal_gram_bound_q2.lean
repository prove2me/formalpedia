-- Prove2me | Theorems.Thm_rademacher_sampled_matrix_noncommutative_khintchine_diagonal_gram_bound_q2
-- name    : rademacher_sampled_matrix_noncommutative_khintchine_diagonal_gram_bound_q2
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-23T02:13:24.212397+00:00
-- url     : https://prove2.me/theorems/3abfa2a5-df3e-48c3-a67f-34b4ad8ee70d
-- statement:
--   Corrected (q≥2) noncommutative Khintchine / Lust-Picquard–Pisier–Buchholz bound for the Rademacher coordinate sum $S_\varepsilon=p^{-1}\sum_{(i,j)\in\Omega}\varepsilon_{ij}X_{ij}e_ie_j^\top$. There is an absolute constant $C>0$ such that for every $\beta>2$ and every $q$ with $q\ge 2$ and $q\ge\beta\log(\max(n_1,n_2))$, the $q$-th Schatten moment satisfies $\mathbb{E}_\varepsilon\,\|S_\varepsilon\|_{S_q}^q \le (C\sqrt q\,\max(G_{\mathrm{row}},G_{\mathrm{col}}))^q$, where $G_{\mathrm{row}},G_{\mathrm{col}}$ are the diagonal Gram Schatten-$q$ norms $\|(\sum_{ij}A_{ij}A_{ij}^\top)^{1/2}\|_{S_q}$ and $\|(\sum_{ij}A_{ij}^\top A_{ij})^{1/2}\|_{S_q}$ of the coordinate matrices $A_{ij}=p^{-1}[(i,j)\in\Omega]X_{ij}e_ie_j^\top$. This is the corrected form of the $q\ge 1$ node: the noncommutative Khintchine inequality (Lust-Picquard–Pisier; Buchholz, constant $2^{-1/4}\sqrt{\pi/e}$) is valid for Schatten exponents $2\le q<\infty$, so the genuine hypothesis is $q\ge 2$ (Candès–Recht 2009, arXiv:0805.4471, Lemma 6.1, §6.1, p.24).
-- source:
--   Candès–Recht 2009, arXiv:0805.4471, Lemma 6.1 (§6.1, p.24); Lust-Picquard–Pisier / Buchholz noncommutative Khintchine inequality (valid for 2≤q<∞).

import Definitions.Def_matrix_completion_gram_schatten
open MatrixCompletion

theorem rademacher_sampled_matrix_noncommutative_khintchine_diagonal_gram_bound_q2 :
    ∃ C : ℝ, 0 < C ∧
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
          (C * Real.sqrt (q : ℝ) *
            max (sampledRowGramSchatten Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X (q : ℝ))
                (sampledColumnGramSchatten Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X (q : ℝ))) ^ q := by
  sorry
