-- Prove2me | Theorems.Thm_mme_finite_rational_certificate_common_square_scale
-- name    : mme_finite_rational_certificate_common_square_scale
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-30T21:10:41.574326+00:00
-- url     : https://prove2.me/theorems/1787e5ae-56cb-4e74-9442-c4b4fa4e2f19
-- title:
--   One common square scale for finite rational certificates and their linear constraints
-- statement:
--   For any finite family of nonnegative rational entries $q_i$, there is a positive integer $D$ and natural entries $a_i=Dq_i$. At every square scale $k^2$, their replicated natural counts equal $k^2Dq_i$ exactly. Every rational linear equation in the entries is preserved under this replication, and every strictly positive entry becomes a strictly positive count whenever $k>0$.
--
--   The finite index family may be a disjoint union of all regional sizes, split counts, mode histograms, and joint-support tables across a finite recursive profile tree. Thus a single denominator suffices for all levels and all joint marginals, rather than choosing incompatible denominators independently. Exact mass equations and joint-marginal equations are instances of the preserved linear constraints. This is an integerization interface; it does not prove feasibility, nonlinear rate inequalities, or coordinate routing for a particular numerical candidate.
-- source:
--   Generalization of the finite-denominator argument in mme_rational_regional_profiles_common_integer_scale (6de83ae3-6a77-47a6-b21e-79cb68fea040). The extension simultaneously includes joint tables and all finite profile layers. Auxiliary certificate preparation for the AlphaEvolve mission; not a verbatim theorem from the paper.

import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
set_option autoImplicit false

theorem mme_finite_rational_certificate_common_square_scale
    {I : Type*} [Fintype I] (q : I → ℚ) (hq : ∀ i, 0 ≤ q i) :
    ∃ D : ℕ, 0 < D ∧ ∃ a : I → ℕ,
      (∀ i, (a i : ℚ) = (D : ℚ) * q i) ∧
      (∀ k : ℕ, ∀ i, ((k ^ 2 * a i : ℕ) : ℚ) = ((k ^ 2 * D : ℕ) : ℚ) * q i) ∧
      (∀ k : ℕ, ∀ coeff : I → ℚ, ∀ target : ℚ,
        (∑ i, coeff i * q i) = target →
        (∑ i, coeff i * ((k ^ 2 * a i : ℕ) : ℚ)) =
          ((k ^ 2 * D : ℕ) : ℚ) * target) ∧
      (∀ k : ℕ, 0 < k → ∀ i, 0 < q i → 0 < k ^ 2 * a i) := by sorry
