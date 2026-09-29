-- Prove2me | Theorems.Thm_Wolf_exists_const_polynomial_bounds_of_generating
-- name    : Wolf.exists_const_polynomial_bounds_of_generating
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-20T16:30:05.136144+00:00
-- url     : https://prove2.me/theorems/a4acc539-d82b-4730-a81d-59022665b6b4
-- title:
--   Lemma 3.5: polynomial growth bounds do not depend on the generating set
-- statement:
--   Let $S$ and $T$ be finite generating sets for the same group $\Gamma$. If there are
--   constants $0 < b_1 \le b_2$ and natural numbers $p \le q$ with
--   $b_1 m^p \le g_T(m) \le b_2 m^q$ for every $m \ge 1$, then there are constants $0 < c_1 \le c_2$
--   with $c_1 m^p \le g_S(m) \le c_2 m^q$ for every $m \ge 1$.
-- source:
--   Wolf, J. A., Growth of finitely generated solvable groups and curvature of Riemannian manifolds, Journal of Differential Geometry 2 (1968) 421–446, https://doi.org/10.4310/jdg/1214428658, Lemma 3.5, p. 427

import Definitions.Def_Chou_Growth
import Definitions.Def_MilnorWolf_Growth
import Mathlib

namespace Wolf

theorem exists_const_polynomial_bounds_of_generating {Γ : Type*} [Group Γ] (S T : Finset Γ)
    (hS : Subgroup.closure (S : Set Γ) = ⊤) (hT : Subgroup.closure (T : Set Γ) = ⊤)
    (b₁ b₂ : ℝ) (hb₁ : 0 < b₁) (hb : b₁ ≤ b₂) (p q : ℕ) (hpq : p ≤ q)
    (hbounds : ∀ m : ℕ, 1 ≤ m →
      b₁ * (m : ℝ) ^ p ≤ (MilnorWolf.growthFunction T m : ℝ) ∧ (MilnorWolf.growthFunction T m : ℝ) ≤ b₂ * (m : ℝ) ^ q) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ ∀ m : ℕ, 1 ≤ m →
      c₁ * (m : ℝ) ^ p ≤ (MilnorWolf.growthFunction S m : ℝ) ∧
        (MilnorWolf.growthFunction S m : ℝ) ≤ c₂ * (m : ℝ) ^ q := by
  sorry

end Wolf
