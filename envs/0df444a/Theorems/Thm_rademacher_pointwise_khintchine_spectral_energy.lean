-- Prove2me | Theorems.Thm_rademacher_pointwise_khintchine_spectral_energy
-- name    : rademacher_pointwise_khintchine_spectral_energy
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-25T09:28:41.267703+00:00
-- url     : https://prove2.me/theorems/81d94d2f-c69d-4545-b55c-d7be300a6cb1
-- statement:
--   Pointwise conditional noncommutative-Khintchine bound for the centered matrix-completion sampling fluctuation. For a FIXED observation set $\Omega$, there is a universal constant $C_{kh}>0$ such that for all $\beta>2$, dimensions $n_1,n_2>0$, sample budget $m$, exponent $q\ge 1$ with $q\ge\beta\log(\max(n_1,n_2))$, and matrix $X$, the Rademacher (conditional sign) expectation of the spectral $q$-th moment of the symmetrized sampled matrix $\mathrm{rademacherSampledMatrix}\,\Omega\,\varepsilon\,p\,X$ (with $p=m/(n_1 n_2)$) is bounded by $(C_{kh}\,\sqrt{q}\,p^{-1}\,\sqrt{\max(\text{row energy},\text{column energy})})^{q}$. This is the conditional Khintchine variance-scale estimate obtained from the Tropp dimension-weighted even-$2n$ Schatten moment engine composed with the Hermitian dilation, the spectral-le-Schatten bridge, and the window factor $n^{1/q}\le e$.
-- source:
--   Candes-Recht 2009 Exact Matrix Completion, Section 6.1 (noncommutative Khintchine); Tropp user-friendly tail bounds.

import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion

theorem rademacher_pointwise_khintchine_spectral_energy :
    ∃ Ckh : ℝ, 0 < Ckh ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ)
        (Omega : Finset (Fin n₁ × Fin n₂)),
        0 < n₁ → 0 < n₂ →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        rademacherExpectation
            (fun eps =>
              MatrixCompletion.spectralNorm
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (Ckh * Real.sqrt (q : ℝ) *
            (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
            Real.sqrt
              (max (sampledRowEnergyMax Omega X)
                (sampledColumnEnergyMax Omega X))) ^ q := by
  sorry
