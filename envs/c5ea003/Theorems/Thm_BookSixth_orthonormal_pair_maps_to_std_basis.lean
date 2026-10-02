-- Prove2me | Theorems.Thm_BookSixth_orthonormal_pair_maps_to_std_basis
-- name    : BookSixth.orthonormal_pair_maps_to_std_basis
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-26T02:35:18.05695+00:00
-- url     : https://prove2.me/theorems/b13a978a-ef6b-4667-8bbc-4b6f25fd6cf2
-- title:
--   Chapter 15: an orthonormal pair of directions aligns with the standard basis by an inner-product-preserving map
-- statement:
--   Any orthonormal pair of directions in $\mathbb{R}^3$ is carried to the first two standard basis vectors by a single linear map that preserves the Euclidean inner product, i.e. by a scaled orthogonal map. If $u$ and $v$ are unit and orthogonal, there is a linear map $A$ with $A u = e_0$ and $A v = e_1$ such that $x \cdot y = (A x) \cdot (A y)$ for all $x, y$. The reason is that an orthonormal pair of vectors in $\mathbb{R}^3$ extends to an orthonormal triple, and any two orthonormal bases of $\mathbb{R}^3$ are related by a unique inner-product-preserving linear map; sending the standard basis to the extended triple and taking the inverse gives the required $A$. This is the linear algebra that `BookSixth.standardizing_time_maps_are_similarities` needs: once the directions $u, v$ of a `RoundCircle` witness $(c, u, v, r)$ are aligned with $e_0, e_1$ by one orthogonal map, the standardising motion is a positive scaling composed with a path of orthogonal maps, and `BookSixth.roundness_of_rigid_similarity_isotopy` then supplies roundness at every time. Note that the map is scaled orthogonal rather than merely orthogonal or merely scalar, consistent with the accepted disproofs of `BookSixth.single_standardize_pointwise` and `BookSixth.single_standardize_is_rigid`.
-- source:
--   Proofs from THE BOOK, Chapter 15 (Aigner-Ziegler), geometric motion of perfect circles; the alignment step preceding the standardising isotopy.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.orthonormal_pair_maps_to_std_basis (u v : Space3)
    (hu : (∑ i, u i * u i) = 1) (hv : (∑ i, v i * v i) = 1) (huv : (∑ i, u i * v i) = 0) :
    ∃ A : Space3 →L[ℝ] Space3,
      (∀ x y : Space3, (∑ i, (A x) i * (A y) i) = ∑ i, x i * y i) ∧
      A u = ![1, 0, 0] ∧
      A v = ![0, 1, 0] := by sorry
