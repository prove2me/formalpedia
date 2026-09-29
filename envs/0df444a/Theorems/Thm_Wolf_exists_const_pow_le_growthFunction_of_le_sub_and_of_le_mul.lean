-- Prove2me | Theorems.Thm_Wolf_exists_const_pow_le_growthFunction_of_le_sub_and_of_le_mul
-- name    : Wolf.exists_const_pow_le_growthFunction_of_le_sub_and_of_le_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-20T16:29:39.753286+00:00
-- url     : https://prove2.me/theorems/54a8b6b2-c699-4cd5-a4b4-ed4bb7c1b3ae
-- title:
--   Lemma 3.4: two rescalings of a polynomial lower bound on the growth function
-- statement:
--   Let $S$ be a finite subset of a group $\Gamma$ and $g_S$ its growth function. Two
--   rescalings of a polynomial lower bound: if $g_S(m) \ge c(m - r)^q$ for all $m \ge 1$, with $c > 0$
--   and $r, q$ fixed natural numbers, then $g_S(m) \ge c'm^q$ for all $m \ge 1$ and some $c' > 0$; and
--   if $g_S(lm) \ge c(lm)^q$ for all $m \ge 1$, with $l > 0$, then $g_S(m) \ge c''m^q$ for all
--   $m \ge 1$ and some $c'' > 0$.
-- source:
--   Wolf, J. A., Growth of finitely generated solvable groups and curvature of Riemannian manifolds, Journal of Differential Geometry 2 (1968) 421–446, https://doi.org/10.4310/jdg/1214428658, Lemma 3.4, p. 426

import Definitions.Def_Chou_Growth
import Definitions.Def_MilnorWolf_Growth
import Mathlib

namespace Wolf

theorem exists_const_pow_le_growthFunction_of_le_sub_and_of_le_mul {Γ : Type*} [Group Γ] (S : Finset Γ) :
    (∀ (r q : ℕ) (c : ℝ), 0 < c →
        (∀ m : ℕ, 1 ≤ m → c * ((m : ℝ) - (r : ℝ)) ^ q ≤ (MilnorWolf.growthFunction S m : ℝ)) →
        ∃ c' : ℝ, 0 < c' ∧ ∀ m : ℕ, 1 ≤ m → c' * (m : ℝ) ^ q ≤ (MilnorWolf.growthFunction S m : ℝ)) ∧
      (∀ (l q : ℕ) (c : ℝ), 0 < l → 0 < c →
        (∀ m : ℕ, 1 ≤ m → c * ((l * m : ℕ) : ℝ) ^ q ≤ (MilnorWolf.growthFunction S (l * m) : ℝ)) →
        ∃ c'' : ℝ, 0 < c'' ∧ ∀ m : ℕ, 1 ≤ m → c'' * (m : ℝ) ^ q ≤ (MilnorWolf.growthFunction S m : ℝ)) := by
  sorry

end Wolf
