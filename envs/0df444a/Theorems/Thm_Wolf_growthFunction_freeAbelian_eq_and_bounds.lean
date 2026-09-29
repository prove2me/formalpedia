-- Prove2me | Theorems.Thm_Wolf_growthFunction_freeAbelian_eq_and_bounds
-- name    : Wolf.growthFunction_freeAbelian_eq_and_bounds
-- status  : Disproved
-- author  : @dbenbenn
-- created : 2026-09-20T16:30:34.466894+00:00
-- url     : https://prove2.me/theorems/43c7cc8a-616c-4d60-9aa2-21927ef2e185
-- title:
--   Proposition 3.6: the growth function of a free abelian group of rank $n$
-- statement:
--   Let $\Gamma$ be free abelian of rank $n$, taken as $\mathbb Z^n$ written
--   multiplicatively, and let $T$ be a minimal generating set, that is, a generating set no proper
--   subset of which generates. Then $g_T(m) = \sum_{l=0}^{n} 2^l \binom{n}{l}\binom{m}{l}$ for every
--   $m$; and for any finite generating set $S$ there are constants $0 < c_1 \le c_2$ with
--   $c_1 m^n \le g_S(m) \le c_2 m^n$ for every $m \ge 1$.
-- source:
--   Wolf, J. A., Growth of finitely generated solvable groups and curvature of Riemannian manifolds, Journal of Differential Geometry 2 (1968) 421–446, https://doi.org/10.4310/jdg/1214428658, Proposition 3.6, p. 427

import Definitions.Def_Chou_Growth
import Definitions.Def_MilnorWolf_Growth
import Mathlib

namespace Wolf

theorem growthFunction_freeAbelian_eq_and_bounds (n : ℕ)
    (T : Finset (Multiplicative (Fin n → ℤ)))
    (hT : Subgroup.closure (T : Set (Multiplicative (Fin n → ℤ))) = ⊤)
    (hmin : ∀ T' ⊂ T, Subgroup.closure (T' : Set (Multiplicative (Fin n → ℤ))) ≠ ⊤) :
    (∀ m : ℕ, MilnorWolf.growthFunction T m = ∑ l ∈ Finset.range (n + 1), 2 ^ l * n.choose l * m.choose l) ∧
      ∀ S : Finset (Multiplicative (Fin n → ℤ)),
        Subgroup.closure (S : Set (Multiplicative (Fin n → ℤ))) = ⊤ →
        ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ ∀ m : ℕ, 1 ≤ m →
          c₁ * (m : ℝ) ^ n ≤ (MilnorWolf.growthFunction S m : ℝ) ∧
            (MilnorWolf.growthFunction S m : ℝ) ≤ c₂ * (m : ℝ) ^ n := by
  sorry

end Wolf
