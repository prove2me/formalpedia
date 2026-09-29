-- Prove2me | Theorems.Thm_Wolf_growth_dichotomy_of_isPolycyclic
-- name    : Wolf.growth_dichotomy_of_isPolycyclic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-20T16:32:56.152069+00:00
-- url     : https://prove2.me/theorems/40d856f1-29ec-428c-aa32-a5c07a0458d4
-- title:
--   Theorem 4.3: a polycyclic group has polynomial growth or exponential growth
-- statement:
--   Let $\Gamma$ be polycyclic and $S$ a finite generating set. If $\Gamma$ has a nilpotent
--   subgroup $\Delta$ of finite index, then $c_1 m^{E_1(\Delta)} \le g_S(m) \le c_2 m^{E_2(\Delta)}$ for
--   constants $0 < c_1 \le c_2$ and every $m \ge 1$, so $\Gamma$ has polynomial growth of degree
--   $\le E_2(\Delta)$. If $\Gamma$ has no nilpotent subgroup of finite index, then
--   $v^m \le g_S(m) \le g_S(1)^m$ for some $v > 1$ and every $m \ge 1$, so $\Gamma$ has exponential
--   growth.
-- source:
--   Wolf, J. A., Growth of finitely generated solvable groups and curvature of Riemannian manifolds, Journal of Differential Geometry 2 (1968) 421–446, https://doi.org/10.4310/jdg/1214428658, Theorem 4.3, p. 434

import Definitions.Def_Chou_Growth
import Definitions.Def_MilnorWolf_Growth
import Mathlib

namespace Wolf

theorem growth_dichotomy_of_isPolycyclic {Γ : Type*} [Group Γ] (h : MilnorWolf.IsPolycyclic Γ)
    (S : Finset Γ) (hS : Subgroup.closure (S : Set Γ) = ⊤) :
    (∀ Δ : Subgroup Γ, Group.IsNilpotent Δ → Δ.FiniteIndex →
        (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ ∀ m : ℕ, 1 ≤ m →
            c₁ * (m : ℝ) ^ (MilnorWolf.growthExponentOne Δ) ≤
                (MilnorWolf.growthFunction S m : ℝ) ∧
              (MilnorWolf.growthFunction S m : ℝ) ≤
                c₂ * (m : ℝ) ^ (MilnorWolf.growthExponentTwo Δ)) ∧
          MilnorWolf.HasPolynomialGrowthOfDegreeLE Γ (MilnorWolf.growthExponentTwo Δ)) ∧
      ((¬ ∃ Δ : Subgroup Γ, Group.IsNilpotent Δ ∧ Δ.FiniteIndex) →
        (∃ v : ℝ, 1 < v ∧ ∀ m : ℕ, 1 ≤ m →
            v ^ m ≤ (MilnorWolf.growthFunction S m : ℝ) ∧
              (MilnorWolf.growthFunction S m : ℝ) ≤ (MilnorWolf.growthFunction S 1 : ℝ) ^ m) ∧
          Chou.HasExponentialGrowth Γ) := by
  sorry

end Wolf
