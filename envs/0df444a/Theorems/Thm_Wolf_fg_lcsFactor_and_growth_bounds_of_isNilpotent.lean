-- Prove2me | Theorems.Thm_Wolf_fg_lcsFactor_and_growth_bounds_of_isNilpotent
-- name    : Wolf.fg_lcsFactor_and_growth_bounds_of_isNilpotent
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-20T16:31:26.802553+00:00
-- url     : https://prove2.me/theorems/4ffa73ec-d92f-4b30-95ad-f5dea86fd578
-- title:
--   Theorem 3.2: a finitely generated nilpotent group has polynomial growth between $m^{E_1}$ and $m^{E_2}$
-- statement:
--   Let $\Gamma$ be a finitely generated nilpotent group. Each factor
--   $\Gamma_k/\Gamma_{k+1}$ of the lower central series is a finitely generated abelian group; writing
--   $n_k$ for the rank of its free part, set $E_1 = \sum_k (k+1)n_k$ and $E_2 = \sum_k 2^k n_k$, the
--   sums running over the factors of the series. Then
--   for any finite generating set $S$ there are constants $0 < c_1 \le c_2$ with
--   $c_1 m^{E_1} \le g_S(m) \le c_2 m^{E_2}$ for every $m \ge 1$.
-- source:
--   Wolf, J. A., Growth of finitely generated solvable groups and curvature of Riemannian manifolds, Journal of Differential Geometry 2 (1968) 421–446, https://doi.org/10.4310/jdg/1214428658, Theorem 3.2, p. 426, with the growth exponents of (3.3)

import Definitions.Def_Chou_Growth
import Definitions.Def_MilnorWolf_Growth
import Mathlib

namespace Wolf

theorem fg_lcsFactor_and_growth_bounds_of_isNilpotent {Γ : Type*} [Group Γ] [Group.FG Γ]
    [Group.IsNilpotent Γ] (S : Finset Γ) (hS : Subgroup.closure (S : Set Γ) = ⊤) :
    (∀ k : ℕ, Group.FG (MilnorWolf.lcsFactor Γ k)) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ ∀ m : ℕ, 1 ≤ m →
        c₁ * (m : ℝ) ^ (MilnorWolf.growthExponentOne Γ) ≤ (MilnorWolf.growthFunction S m : ℝ) ∧
          (MilnorWolf.growthFunction S m : ℝ) ≤
            c₂ * (m : ℝ) ^ (MilnorWolf.growthExponentTwo Γ) := by
  sorry

end Wolf
