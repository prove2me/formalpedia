-- Prove2me | Theorems.Thm_Wolf_growthFunction_freeAbelian_eq_and_bounds_of_card
-- name    : Wolf.growthFunction_freeAbelian_eq_and_bounds_of_card
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-20T19:35:56.613315+00:00
-- url     : https://prove2.me/theorems/c41efbe1-e7de-41f7-9418-a6cd6d46dd33
-- title:
--   Proposition 3.6: the growth function of a free abelian group of rank $n$
-- statement:
--   Let $\Gamma$ be free abelian of rank $n$, taken as $\mathbb Z^n$ written
--   multiplicatively, and let $T$ be a generating set with exactly $n$ elements. Then
--   $g_T(m) = \sum_{l=0}^{n} 2^l \binom{n}{l}\binom{m}{l}$ for every $m$; and for any finite
--   generating set $S$ there are constants $0 < c_1 \le c_2$ with $c_1 m^n \le g_S(m) \le c_2 m^n$
--   for every $m \ge 1$.
--
--   The cardinality hypothesis is Wolf's "minimal generating set", which the paper's notation
--   $T = \{\tau_1, \ldots, \tau_n\}$ fixes at $n$ elements; a generating set of $\mathbb Z^n$ with $n$
--   elements is a basis. It is not enough to ask that no proper subset of $T$ generate: $\{2, 3\}$
--   generates $\mathbb Z$, no proper subset does, and the ball of radius one is $\{0, \pm 2, \pm 3\}$,
--   of size five, where the formula gives three. The closed form depends on $T$ being a basis; the
--   bounds in the second half hold for every finite generating set.
-- source:
--   Wolf, J. A., Growth of finitely generated solvable groups and curvature of Riemannian manifolds, Journal of Differential Geometry 2 (1968) 421–446, https://doi.org/10.4310/jdg/1214428658, Proposition 3.6, p. 427

import Definitions.Def_MilnorWolf_Growth
import Mathlib

namespace Wolf

theorem growthFunction_freeAbelian_eq_and_bounds_of_card (n : ℕ)
    (T : Finset (Multiplicative (Fin n → ℤ)))
    (hT : Subgroup.closure (T : Set (Multiplicative (Fin n → ℤ))) = ⊤)
    (hcard : T.card = n) :
    (∀ m : ℕ, MilnorWolf.growthFunction T m = ∑ l ∈ Finset.range (n + 1), 2 ^ l * n.choose l * m.choose l) ∧
      ∀ S : Finset (Multiplicative (Fin n → ℤ)),
        Subgroup.closure (S : Set (Multiplicative (Fin n → ℤ))) = ⊤ →
        ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ ∀ m : ℕ, 1 ≤ m →
          c₁ * (m : ℝ) ^ n ≤ (MilnorWolf.growthFunction S m : ℝ) ∧
            (MilnorWolf.growthFunction S m : ℝ) ≤ c₂ * (m : ℝ) ^ n := by
  sorry

end Wolf
