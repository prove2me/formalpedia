-- Prove2me | Theorems.Thm_conditional_khintchine_scale_moment_from_row_column_energy_moment_2pN
-- name    : conditional_khintchine_scale_moment_from_row_column_energy_moment_2pN
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-25T09:33:52.647067+00:00
-- url     : https://prove2.me/theorems/68a87430-f5b0-45e7-91c5-ff37279cfeb1
-- statement:
--   Conversion of the Bernoulli moment of the conditional Khintchine variance scale into the displayed $\sqrt{qN/p}\,\|X\|_\infty$ log-moment bound, in the wider moment window $q\le 2(pN)$ (with $p=m/(n_1n_2)$, $N=\max(n_1,n_2)$). Given positive constants $C_{energy},C_{kh}$, there is $C_{rad}>0$ such that for all $\beta>2$, dimensions $n_1,n_2>0$, $m\le n_1n_2$, $m\ge\beta N\log N$, exponent $q\ge1$ with $\beta\log N\le q\le 2\beta\log N$ and $q\le 2(pN)$, and matrix $X$: if the Bernoulli expectation of the $q$-th power of the maximal row/column sampled energy is bounded by $(C_{energy}\,p\,N\,\|X\|_\infty^2)^q$, then the Bernoulli expectation of the conditional Khintchine scale $q$-moment $(C_{kh}\sqrt q\,p^{-1}\sqrt{\max\text{energy}})^q$ is bounded by $(C_{rad}\sqrt{qN/p}\,\|X\|_\infty)^q$. This is the $q\le 2(pN)$ variant of Lemma 6.2's energy power-mean step required by the $\_2pN$ master conversion.
-- source:
--   Candes-Recht 2009 Exact Matrix Completion, Section 6.1, Lemma 6.2 (energy power-mean step), wide moment window q<=2(pN).

import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion

theorem conditional_khintchine_scale_moment_from_row_column_energy_moment_2pN
    (Cenergy Ckh : ℝ) :
    0 < Cenergy →
    0 < Ckh →
    ∃ Crad : ℝ, 0 < Crad ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) →
        (q : ℝ) ≤ 2 * (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂))) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              (max (sampledRowEnergyMax Omega X)
                (sampledColumnEnergyMax Omega X)) ^ q) ≤
          (Cenergy * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              (Ckh * Real.sqrt (q : ℝ) *
                (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
                Real.sqrt
                  (max (sampledRowEnergyMax Omega X)
                    (sampledColumnEnergyMax Omega X))) ^ q) ≤
          (Crad * Real.sqrt
            (((q : ℝ) * (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X) ^ q := by
  sorry
