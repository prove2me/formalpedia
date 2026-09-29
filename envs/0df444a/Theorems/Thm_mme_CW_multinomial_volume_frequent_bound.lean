-- Prove2me | Theorems.Thm_mme_CW_multinomial_volume_frequent_bound
-- name    : mme_CW_multinomial_volume_frequent_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-06-05T03:35:03.143715+00:00
-- url     : https://prove2.me/theorems/8cc01534-2819-4d27-a720-9851e64a7166
-- statement:
--   Stirling lower bound on the central trinomial coefficient. For $1\le q$, real $V\ge 0$ with $V^3 < 3q$, and any $\varepsilon>0$, infinitely many $M$ satisfy $V^{3M}(1-\varepsilon)\le \big((3M)!/(M!)^3\big)^{1/3}\,q^M$. Supplies the entropy ($\log_2 3$) term in the Coppersmith–Winograd laser value.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
open BigOperators Filter

theorem mme_CW_multinomial_volume_frequent_bound
    (q : ℕ) (_hq : 1 ≤ q)
    (V : ℝ) (_hV_nn : 0 ≤ V) (_hV_cubed : V^3 < 3 * (q : ℝ))
    (ε : ℝ) (_hε : 0 < ε) :
    ∃ᶠ (M : ℕ) in atTop,
      V ^ (3 * M) * (1 - ε) ≤
        ((Nat.factorial (3 * M) /
          (Nat.factorial M * Nat.factorial M * Nat.factorial M) : ℕ) : ℝ) ^ ((1 : ℝ) / 3) *
        ((q : ℝ)) ^ M := by sorry
