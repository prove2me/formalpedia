-- Prove2me | Theorems.Thm_Hirsch_hpoly_diameter_le_excess_of_projectively_hidden_small_row_blocks
-- name    : Hirsch.hpoly_diameter_le_excess_of_projectively_hidden_small_row_blocks
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-12T18:27:41.994315+00:00
-- url     : https://prove2.me/theorems/b6289eea-78b3-4bcf-a5d7-65fbab46a986
-- title:
--   Hirsch routing for products hidden by a positive projective chart
-- statement:
--   Let $P=\{x\in\mathbb R^d:a_i\cdot x\le b_i,\ 1\le i\le n\}$
--   be nonempty and bounded. Suppose an invertible linear change of coordinates
--   and a partition of all describing rows identify $P$ with independent factors
--   $P_j\subseteq\mathbb R^{d_j}$, each described by $n_j$ rows, where
--   $d_j\le n_j\le d_j+3$. All combinations of factor points must be feasible;
--   the row identities certify an actual Cartesian product.
--
--   Choose $c\in\mathbb R^d$ and define $a'_i=a_i+b_i c$. Suppose there are
--   nonnegative weights $\mu_i,\nu_i$ satisfying
--
--   $$\sum_i\mu_i a_i=-c,\qquad \sum_i\mu_i b_i<1,\qquad
--   \sum_i\nu_i a'_i=c,\qquad \sum_i\nu_i b_i<1.$$
--
--   Then the polyhedron $Q=\{y\in\mathbb R^d:a'_i\cdot y\le b_i\}$ satisfies
--
--   $$\operatorname{diam}_{\mathrm{edge}}(Q)\le n-d.$$
--
--   There is no bound on total excess, number of factors, or repair-support deficit.
--   The criterion includes products hidden by a positive projective transformation,
--   even when the target normals do not split into independent linear blocks.
--   The chart and factorization are supplied and certified; their existence for
--   arbitrary polyhedra is not asserted.
--
--   **Formalization Note** Dimension and row partitions are explicit equivalences.
--   Stationary steps permit padding to exactly $n-d$ steps, with natural subtraction.
--   The certificate checker uses rational data; the theorem permits real coefficients.
-- source:
--   Exact statement, positive chart proof and certificate criterion: https://github.com/jjoshua2/prove2me-work/blob/6cd06d52fa4bbd832d8eae1eddd85ded9f0bfec9/Solutions/PolynomialProjectiveRowBlockRouting.lean . Classical context: Gouveia, Macchia, Thomas, Wiebe, The Slack Realization Space of a Polytope (2019), Section 2, equation (3) and Lemma 2.3, https://arxiv.org/html/1708.04739v4#S2 . The finite multiplier and row-block criterion is derived in the cited Lean source, not claimed to be a verbatim theorem of that paper.

import Mathlib
import Definitions.Def_Hirsch_model
open scoped BigOperators RealInnerProductSpace
open Set Hirsch

namespace Hirsch
theorem hpoly_diameter_le_excess_of_projectively_hidden_small_row_blocks
{d n k : ℕ} (dims counts : Fin k → ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ]
      (∀ i : Fin k, EuclideanSpace ℝ (Fin (dims i))))
    (e : (Σ i : Fin k, Fin (counts i)) ≃ Fin n)
    (A : ∀ i : Fin k, Fin (counts i) → EuclideanSpace ℝ (Fin (dims i)))
    (hrows : ∀ z i j, ⟪a (e ⟨i, j⟩), T.symm z⟫ = ⟪A i j, z i⟫)
    (hbd : Bornology.IsBounded (Hpoly a b)) (hne : (Hpoly a b).Nonempty)
    (hcount : ∀ i, dims i ≤ counts i)
    (hsmallcount : ∀ i, counts i ≤ dims i + 3)
    (c : EuclideanSpace ℝ (Fin d)) (weights inverseWeights : Fin n → ℝ)
    (hweights : ∀ i, 0 ≤ weights i)
    (hnormal : (∑ i, weights i • a i) = -c)
    (hmargin : (∑ i, weights i * b i) < 1)
    (hinverseWeights : ∀ i, 0 ≤ inverseWeights i)
    (hinverseNormal : (∑ i, inverseWeights i • (a i + b i • c)) = c)
    (hinverseMargin : (∑ i, inverseWeights i * b i) < 1) :
    DiamLE (Hpoly (fun i => a i + b i • c) b) (n - d) := by sorry
end Hirsch
