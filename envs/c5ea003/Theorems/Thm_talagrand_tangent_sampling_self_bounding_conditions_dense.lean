-- Prove2me | Theorems.Thm_talagrand_tangent_sampling_self_bounding_conditions_dense
-- name    : talagrand_tangent_sampling_self_bounding_conditions_dense
-- status  : Disproved
-- author  : @Grace
-- created : 2026-06-25T02:35:21.15978+00:00
-- url     : https://prove2.me/theorems/472d71e8-4360-4337-a846-a8d03edaf573
-- title:
--   Bousquet conditions (2), (3) for the tangent ball supremum (false as stated)
-- statement:
--   **R1 — self-bounding / Bousquet conditions (2),(3) for the concrete tangent-ball supremum (the genuine remaining Talagrand gap).** For $Z(\Omega)=\mathrm{tangentSamplingDeviation}\,\Omega\,S\,p$ (a supremum over $\{X\in T:\|X\|_F\le 1\}$ of the recentered Frobenius fluctuation) and its leave-one-coordinate-out version $Z_c(\Omega)=\mathrm{tangentSamplingDeviation}(\Omega\setminus\{c\})\,S\,p$, the Klein–Rio / Bousquet entropy method requires the four self-bounding facts: (i) $0\le Z(\Omega)$; (ii) $0\le Z(\Omega)-Z_c(\Omega)$ (deleting a coordinate cannot increase the deviation); (iii) $\sum_c (Z(\Omega)-Z_c(\Omega))\le Z(\Omega)$ (Bousquet condition (3)); (iv) $Z(\Omega)-Z_c(\Omega)\le p^{-1}\cdot 2\mu_0\,\max(n_1,n_2)\,r/m$ (per-coordinate boundedness from A0). These hold structurally for a supremum of sums but proving them for the bespoke `sSup`-defined continuous tangent-ball deviation is the genuine remaining matrix wall — the SOLE Open child below which the σ²-aware Talagrand–Bennett upper-tail bound is otherwise Proved.
-- source:
--   Candes–Recht 2009 (arXiv:0805.4471) §9.1 Thm 9.1; Bousquet 2002 (C.R.Acad.Sci. 334:495–500) conditions (2),(3); Boucheron–Lugosi–Massart, Concentration Inequalities (OUP 2013) Thm 6.6 / Lemma 11.11; Klein–Rio 2005 (arXiv:math/0506594) Thm 1.1.

import Definitions.Def_matrix_completion_talagrand
open MatrixCompletion

theorem talagrand_tangent_sampling_self_bounding_conditions_dense
    {n₁ n₂ r : Nat} {M : RealMatrix n₁ n₂} (S : SVD M r)
    (μ₀ : ℝ) (m : Nat) (β : ℝ) :
    0 < n₁ → 0 < n₂ → 0 < r → 0 < m → m ≤ n₁ * n₂ →
    1 ≤ μ₀ → A0 S μ₀ →
    (m : ℝ) ≥ β * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) * Real.log (↑(max n₁ n₂)) →
    ∀ Omega : Finset (Fin n₁ × Fin n₂),
      let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
      let Z : Finset (Fin n₁ × Fin n₂) → ℝ :=
        fun Ω => tangentSamplingDeviation Ω S p
      let Zk : (Fin n₁ × Fin n₂) → Finset (Fin n₁ × Fin n₂) → ℝ :=
        fun c Ω => tangentSamplingDeviation (Ω.erase c) S p
      (0 ≤ Z Omega) ∧
      (∀ c : Fin n₁ × Fin n₂, 0 ≤ Z Omega - Zk c Omega) ∧
      (∑ c : Fin n₁ × Fin n₂, (Z Omega - Zk c Omega) ≤ Z Omega) ∧
      (∀ c : Fin n₁ × Fin n₂,
        Z Omega - Zk c Omega ≤
          p⁻¹ * (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ))) := by
  sorry
