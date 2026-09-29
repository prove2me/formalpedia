-- Prove2me | Theorems.Thm_Wolf_growth_dichotomy_of_isSolvable_of_fg
-- name    : Wolf.growth_dichotomy_of_isSolvable_of_fg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-20T16:33:23.403177+00:00
-- url     : https://prove2.me/theorems/8d11a757-69e4-4457-901b-9a692f48dfe2
-- title:
--   Theorem 4.8: the Milnor–Wolf theorem
-- statement:
--   Let $\Gamma$ be a finitely generated solvable group. If $\Gamma$ has a nilpotent subgroup
--   $\Delta$ of finite index, then $\Gamma$ is polycyclic and has polynomial growth of degree
--   $\le E_2(\Delta)$. If $\Gamma$ has no nilpotent subgroup of finite index, then $\Gamma$ has
--   exponential growth.
-- source:
--   Wolf, J. A., Growth of finitely generated solvable groups and curvature of Riemannian manifolds, Journal of Differential Geometry 2 (1968) 421–446, https://doi.org/10.4310/jdg/1214428658, Theorem 4.8, p. 438

import Definitions.Def_Chou_Growth
import Definitions.Def_MilnorWolf_Growth
import Mathlib

namespace Wolf

theorem growth_dichotomy_of_isSolvable_of_fg {Γ : Type*} [Group Γ] [Group.FG Γ]
    [Group.IsSolvable Γ] :
    (∀ Δ : Subgroup Γ, Group.IsNilpotent Δ → Δ.FiniteIndex →
        MilnorWolf.IsPolycyclic Γ ∧
          MilnorWolf.HasPolynomialGrowthOfDegreeLE Γ (MilnorWolf.growthExponentTwo Δ)) ∧
      ((¬ ∃ Δ : Subgroup Γ, Group.IsNilpotent Δ ∧ Δ.FiniteIndex) →
        Chou.HasExponentialGrowth Γ) := by
  sorry

end Wolf
