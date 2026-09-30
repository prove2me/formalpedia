-- Prove2me | Theorems.Thm_Hirsch_minkowski_summand_exposed_route_contraction
-- name    : Hirsch.minkowski_summand_exposed_route_contraction
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-19T01:44:07.650854+00:00
-- url     : https://prove2.me/theorems/9058b830-964e-4c2d-80d7-e17c68e51cb6
-- title:
--   Canonical Minkowski component maps contract original exposed-edge walks
-- statement:
--   For any two convex subsets P,Q of real coordinate space and any finite walk of actual extreme points of their actual Minkowski sum, whose consecutive distinct vertices span whole exposed sum segments, derive the unique decomposition of each walk vertex into extreme component points. Each component segment is a whole exposed face, possibly a singleton, and the component displacements are nonnegative cooriented fractions alpha and 1-alpha of the sum displacement. Construct an exposed/extreme-edge walk in EACH original summand between the corresponding component endpoints, deleting stationary component transitions, with each resulting length at most the original walk length. No component vertices, unique-decomposition map, component supporting faces, parallel directions, or summand edge/route oracle is supplied. P,Q need not be polytopes, bounded, closed, full-dimensional or finite. The finite sum walk and convex Minkowski structure ARE explicit inputs; a short sum walk for an arbitrary polytope or lifts of every independently chosen summand endpoint are not proved. Zero-dimensional and zero-length cases are included. The maps are not arbitrary linear projections. No general Polynomial Hirsch bound is claimed.
-- source:
--   New reverse geometric transfer after #308, distinct from #244 forward fixed-core fibre lifting. The 32-line compress_schedule proof is reused verbatim from ACCEPTED #306 in the new namespace; all geometric proofs are supplied here. Classical summand graph contraction is credited to Antoine Deza and Lionel Pournin, Diameter, decomposability, and Minkowski sums of polytopes, arXiv:1806.07643, Canadian Mathematical Bulletin62(4),2019,741-755, DOI10.4153/S0008439518000668. No historical-priority or newly improved diameter claim. Coordination on #308 comment5738035171; baseline38475846e6cb588434893f912821617892306b29.

import Mathlib
set_option autoImplicit false

theorem Hirsch.minkowski_summand_exposed_route_contraction (d N : ℕ) (P Q : Set (Fin d → ℝ))
    (hP : Convex ℝ P) (hQ : Convex ℝ Q) (z : ℕ → (Fin d → ℝ))
    (hz : ∀ i, i ≤ N → z i ∈
      ({w | ∃ x ∈ P, ∃ y ∈ Q, x+y=w}).extremePoints ℝ)
    (he : ∀ i, i < N → z i ≠ z (i+1) ∧
      IsExposed ℝ {w | ∃ x ∈ P, ∃ y ∈ Q, x+y=w} (segment ℝ (z i) (z (i+1)))) :
    ∃ a b : ℕ → (Fin d → ℝ),
      (∀ i, i ≤ N → a i ∈ P.extremePoints ℝ ∧ b i ∈ Q.extremePoints ℝ ∧
        a i+b i=z i ∧ ∀ x ∈ P, ∀ y ∈ Q, x+y=z i → x=a i ∧ y=b i) ∧
      (∀ i, i < N →
        IsExposed ℝ P (segment ℝ (a i) (a (i+1))) ∧
        IsExposed ℝ Q (segment ℝ (b i) (b (i+1))) ∧
        ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧
          a (i+1)-a i = α • (z (i+1)-z i) ∧
          b (i+1)-b i = (1-α) • (z (i+1)-z i)) ∧
      (∃ L : ℕ, L ≤ N ∧ ∃ p : ℕ → (Fin d → ℝ),
        p 0=a 0 ∧ p L=a N ∧ (∀ i, i ≤ L → p i ∈ P.extremePoints ℝ) ∧
        ∀ i, i < L → p i ≠ p (i+1) ∧
          IsExposed ℝ P (segment ℝ (p i) (p (i+1))) ∧
          IsExtreme ℝ P (segment ℝ (p i) (p (i+1)))) ∧
      (∃ L : ℕ, L ≤ N ∧ ∃ p : ℕ → (Fin d → ℝ),
        p 0=b 0 ∧ p L=b N ∧ (∀ i, i ≤ L → p i ∈ Q.extremePoints ℝ) ∧
        ∀ i, i < L → p i ≠ p (i+1) ∧
          IsExposed ℝ Q (segment ℝ (p i) (p (i+1))) ∧
          IsExtreme ℝ Q (segment ℝ (p i) (p (i+1)))) := by sorry
