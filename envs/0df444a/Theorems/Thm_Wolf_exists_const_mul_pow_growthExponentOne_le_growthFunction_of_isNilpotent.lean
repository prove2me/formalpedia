-- Prove2me | Theorems.Thm_Wolf_exists_const_mul_pow_growthExponentOne_le_growthFunction_of_isNilpotent
-- name    : Wolf.exists_const_mul_pow_growthExponentOne_le_growthFunction_of_isNilpotent
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-20T22:59:28.70882+00:00
-- url     : https://prove2.me/theorems/1cb452d2-dd7e-49bb-b96b-cc1e34347af2
-- title:
--   Theorem 3.2, lower bound: a finitely generated nilpotent group grows at least like $m^{E_1}$
-- statement:
--   Let $\Gamma$ be a finitely generated nilpotent group and let $S$ be any finite
--   generating set. Then there is a constant $c > 0$ such that
--   $$c\,m^{E_1(\Gamma)} \le g_S(m) \qquad \text{for every integer } m \ge 1,$$
--   where $g_S(m)$ is Wolf's growth function, the number of elements of $\Gamma$
--   expressible as a product of at most $m$ factors drawn from $S \cup S^{-1}$.
--
--   Here $n_k$ is the $\mathbb{Z}$-rank of the $k$-th lower central factor,
--   which the published growth bundle realises not literally as $\Gamma_k/\Gamma_{k+1}$ but as the
--   abelianization of $\Gamma_k$ modulo the image of $\Gamma_{k+1} \cap \Gamma_k$ — the same group,
--   presented so that it carries an abelian group structure by construction. The sums run over $k$
--   below the nilpotency class of $\Gamma$, so that they are finite; these are Wolf's exponents
--   (3.3), $E_1 = \sum_k (k+1) n_k$ and $E_2 = \sum_k 2^k n_k$. Note $E_1 \le E_2$, termwise, since
--   $k + 1 \le 2^k$.
--
--   The hypothesis that $\Gamma$ is finitely generated is carried for symmetry with Theorem 3.2 but
--   does no work: it already follows from the existence of the finite generating set $S$, the two
--   having the same shape.
--
--   The constant is allowed to depend on $S$, and the bound is asserted for every finite generating
--   set. Only the lower bound is claimed; nothing is said about an upper bound, and no limit or
--   growth rate is mentioned.
-- source:
--   Wolf, J. A., Growth of finitely generated solvable groups and curvature of Riemannian manifolds, Journal of Differential Geometry 2 (1968) 421–446, https://doi.org/10.4310/jdg/1214428658, Theorem 3.2, p. 426; the lower bound is (3.8), proved on p. 429

import Definitions.Def_MilnorWolf_Growth
import Mathlib

namespace Wolf

theorem exists_const_mul_pow_growthExponentOne_le_growthFunction_of_isNilpotent {Γ : Type*}
    [Group Γ] [Group.FG Γ] [Group.IsNilpotent Γ] (S : Finset Γ)
    (hS : Subgroup.closure (S : Set Γ) = ⊤) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
      c * (m : ℝ) ^ (MilnorWolf.growthExponentOne Γ) ≤ (MilnorWolf.growthFunction S m : ℝ) := by
  sorry

end Wolf
