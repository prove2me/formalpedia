-- Prove2me | Theorems.Thm_Wolf_fg_and_polynomial_growth_of_finiteIndex
-- name    : Wolf.fg_and_polynomial_growth_of_finiteIndex
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-20T16:31:52.08806+00:00
-- url     : https://prove2.me/theorems/d893d643-d810-453d-a600-e43f550d01f0
-- title:
--   Theorem 3.11: a finite-index subgroup is finitely generated, and polynomial growth passes up to the group
-- statement:
--   Let $G$ be a finitely generated group and $H$ a subgroup of finite index. Then $H$ is
--   finitely generated; if $H$ has polynomial growth of degree $\le E$ then so does $G$; and if $H$ is
--   moreover nilpotent with polynomial growth of degree $\le E$, then $G$ has polynomial growth of
--   degree $\le \min(E, E_2(H))$.
--
--   Wolf's $\Sigma$ is written $G$ here and Wolf's $\Gamma$ is written $H$, because $\Sigma$ is reserved
--   notation in Lean.
-- source:
--   Wolf, J. A., Growth of finitely generated solvable groups and curvature of Riemannian manifolds, Journal of Differential Geometry 2 (1968) 421–446, https://doi.org/10.4310/jdg/1214428658, Theorem 3.11, p. 431

import Definitions.Def_Chou_Growth
import Definitions.Def_MilnorWolf_Growth
import Mathlib

namespace Wolf

theorem fg_and_polynomial_growth_of_finiteIndex {G : Type*} [Group G] [Group.FG G] (H : Subgroup G)
    [H.FiniteIndex] :
    Group.FG H ∧
      (∀ E : ℕ, MilnorWolf.HasPolynomialGrowthOfDegreeLE H E →
        MilnorWolf.HasPolynomialGrowthOfDegreeLE G E) ∧
      (Group.IsNilpotent H → ∀ E : ℕ, MilnorWolf.HasPolynomialGrowthOfDegreeLE H E →
        MilnorWolf.HasPolynomialGrowthOfDegreeLE G (min E (MilnorWolf.growthExponentTwo H))) := by
  sorry

end Wolf
