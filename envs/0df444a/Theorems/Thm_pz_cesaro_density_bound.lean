-- Prove2me | Theorems.Thm_pz_cesaro_density_bound
-- name    : pz_cesaro_density_bound
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T11:29:17.949345+00:00
-- url     : https://prove2.me/theorems/db06e4a1-732f-48e8-87ff-790297e129cb
-- title:
--   Paley-Zygmund Cesaro density step
-- statement:
--   A pure real-analysis step of Paley-Zygmund type. Given $K \ge 0$ and a tolerance $\rho' > 0$ there is a threshold $M$ such that whenever $\Lambda \ge M$, $0 \le A \le \Lambda^{3/2}$, a mean $\alpha$ satisfies $\Lambda - 1 \le \alpha \le K + \sqrt{\beta(1-d)}$, the second moment satisfies $\beta \le \Lambda^2 + A/2 + 1$, and $0 \le d \le 1$, then $d \le \rho'$. Here $d$ plays the role of the Cesaro density of a sublevel set, $\alpha$ and $\beta$ the first two Cesaro moments of a nonnegative function, and $\Lambda$ its limiting mean.

import Mathlib

theorem pz_cesaro_density_bound :
  ∀ K : Real, 0 ≤ K → ∀ ρ' : Real, 0 < ρ' →
    ∃ M : Real, ∀ Λ A α β d : Real, M ≤ Λ → 0 ≤ A → A ≤ Λ * Real.sqrt Λ →
      Λ - 1 ≤ α → α ≤ K + Real.sqrt (β * (1 - d)) →
      β ≤ Λ^2 + A / 2 + 1 → 0 ≤ d → d ≤ 1 → d ≤ ρ' := by
  sorry
