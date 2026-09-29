-- Prove2me | Theorems.Thm_polyDegree_alternating_sum_witness
-- name    : polyDegree_alternating_sum_witness
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-06T20:39:26.613018+00:00
-- url     : https://prove2.me/theorems/4af068d5-d672-44ca-b6ae-0012a21df61e
-- statement:
--   **Polynomial-degree witness via non-zero Möbius alternating sum.**
--
--   For every Boolean function $f : \{0,1\}^n \to \{0,1\}$ with $\deg(f) \ge 1$, there is an index set $S \subseteq \{1, \ldots, n\}$ with $|S| = \deg(f)$ whose Möbius alternating sum is non-zero:
--   $$\sum_{T \subseteq S} (-1)^{|S| - |T|} \cdot \mathbf{1}\!\left[ f(\chi_T) \right] \;\ne\; 0,$$
--   where $\chi_T \in \{0,1\}^n$ is the indicator vector of $T$ (so $\chi_T(i) = 1$ iff $i \in T$) and $\mathbf{1}[\cdot]$ converts a Boolean to $\{0,1\} \subset \mathbb{R}$.
--
--   Equivalently, the canonical multilinear interpolant of $f$ has a non-zero coefficient on the squarefree monomial $\prod_{i \in S} x_i$. This is the "$\ge$" half of $\deg(f) = \max\{|S| : \mathrm{altSum}_S(f) \ne 0\}$.
-- source:
--   Gotsman, Chaim, and Nathan Linial. "The equivalence of two problems on the cube." Journal of Combinatorial Theory, Series A 61.1 (1992): 142-146. (Direction used in Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.)

import Definitions.Def_BoolFunc
import Definitions.Def_polyDegree
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic

/-!
# Witness monomial for `polyDegree`: non-zero alternating sum

If `f : BoolFunc n` has positive polynomial degree `d`, then there
exists a `d`-element index set `S ⊆ [n]` whose Möbius alternating
sum (the coefficient of `∏_{i ∈ S} xᵢ` in `interpolant f`) is
non-zero. Equivalently: every multilinear polynomial representing
`f` has a non-zero degree-`d` monomial supported on `S`.
-/

/-- For any `f : BoolFunc n` with `polyDegree f ≥ 1`, there is an
    index set `S` of size `polyDegree f` whose Boolean Möbius
    alternating sum is non-zero. -/

theorem polyDegree_alternating_sum_witness
    {n : ℕ} (f : BoolFunc n) (h_pos : 1 ≤ polyDegree f) :
    ∃ S : Finset (Fin n), S.card = polyDegree f ∧
      (∑ T ∈ S.powerset,
          (if (S.card - T.card) % 2 = 0 then (1 : ℝ) else -1) *
          (if f (fun i => decide (i ∈ T)) then (1 : ℝ) else 0))
        ≠ 0 := by sorry
