-- Prove2me | Theorems.Thm_Wolf_exists_growthFunction_le_const_mul_pow_growthExponentTwo_of_isNilpotent
-- name    : Wolf.exists_growthFunction_le_const_mul_pow_growthExponentTwo_of_isNilpotent
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-20T23:00:00.430861+00:00
-- url     : https://prove2.me/theorems/166d431e-192d-445a-a411-a8adabdf39cc
-- title:
--   Theorem 3.2, upper bound: a finitely generated nilpotent group grows at most like $m^{E_2}$
-- statement:
--   Let $\Gamma$ be a finitely generated nilpotent group and let $S$ be any finite
--   generating set. Then there is a constant $c > 0$ such that
--   $$g_S(m) \le c\,m^{E_2(\Gamma)} \qquad \text{for every integer } m \ge 1,$$
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
--   set. Only the upper bound is claimed. It is stronger than the published predicate for polynomial
--   growth of degree $\le E_2$, which asks for the bound on *some* generating set rather than on
--   every one.
-- source:
--   Wolf, J. A., Growth of finitely generated solvable groups and curvature of Riemannian manifolds, Journal of Differential Geometry 2 (1968) 421–446, https://doi.org/10.4310/jdg/1214428658, Theorem 3.2, p. 426; the upper bound is the normal form (3.9), p. 429, with the estimate (3.10), pp. 430–431

import Definitions.Def_MilnorWolf_Growth
import Mathlib

namespace Wolf

theorem exists_growthFunction_le_const_mul_pow_growthExponentTwo_of_isNilpotent {Γ : Type*}
    [Group Γ] [Group.FG Γ] [Group.IsNilpotent Γ] (S : Finset Γ)
    (hS : Subgroup.closure (S : Set Γ) = ⊤) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
      (MilnorWolf.growthFunction S m : ℝ) ≤ c * (m : ℝ) ^ (MilnorWolf.growthExponentTwo Γ) := by
  sorry

end Wolf
