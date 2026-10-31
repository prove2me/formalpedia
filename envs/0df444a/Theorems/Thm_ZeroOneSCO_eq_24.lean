-- Prove2me | Theorems.Thm_ZeroOneSCO_eq_24
-- name    : ZeroOneSCO.eq_24
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:52:25.238246+00:00
-- url     : https://prove2.me/theorems/93f2706c-69a9-4705-8641-1d8fa05fa41d
-- title:
--   Display (24): column-wise complementarity
-- statement:
--   Let $Z,W\in\mathbb R^{M\times N}$, $\tau>0$ and $n\in\mathcal N$. Then
--   $$
--   0\ge Z_{:n}\perp W_{:n}\ge0\iff (Z_{:n}+\tau W_{:n})^-=Z_{:n},
--   $$
--   and each of these implies $\|(Z_{:n}+\tau W_{:n})^+\|=\tau\|W_{:n}\|$. Here $0\ge A\perp B\ge0$ means that $0\ge A_{mn}$, $B_{mn}\ge 0$ and $A_{mn}B_{mn}=0$ for all entries.
--
--   This elementary fact translates the complementarity in the stationarity conditions into the projection formula.
--
--   Differences from the source:
--   - encoding: column indices in 𝓜 = {1,…,M}, 𝓝 = {1,…,N} → Fin M, Fin N (0-based); reason: Lean convention
-- source:
--   Zhou, Pan, Xiu & Li, A 0/1 Constrained Optimization Solving Sample Average Approximation for Chance Constrained Programming, arXiv:2210.11889v5, (24), p.8

import Mathlib
import Definitions.Def_ZeroOneSCO_Columns

namespace ZeroOneSCO

/-- Display (24), Zhou, Pan, Xiu & Li, arXiv:2210.11889v5, p.8: for `τ > 0` and every column `n`,
`0 ≥ Z_{:n} ⊥ W_{:n} ≥ 0` (notation of p.5) holds if and only if `(Z_{:n} + τW_{:n})⁻ = Z_{:n}`, and it
implies `‖(Z_{:n} + τW_{:n})⁺‖ = τ‖W_{:n}‖`. -/
theorem eq_24 {M N : ℕ} (Z W : Mat M N) (τ : ℝ) (hτ : 0 < τ) (n : Fin N) :
    ((∀ m, Z m n ≤ 0 ∧ 0 ≤ W m n ∧ Z m n * W m n = 0) ↔
        ∀ m, min (Z m n + τ * W m n) 0 = Z m n) ∧
      ((∀ m, Z m n ≤ 0 ∧ 0 ≤ W m n ∧ Z m n * W m n = 0) →
        colPosNorm (Z + τ • W) n = τ * colNorm W n) := by sorry

end ZeroOneSCO
