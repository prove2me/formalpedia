-- Prove2me | Theorems.Thm_Hirsch_segment_summand_equality_of_farkas_certificates
-- name    : Hirsch.segment_summand_equality_of_farkas_certificates
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-13T18:42:38.734067+00:00
-- url     : https://prove2.me/theorems/2eaa5e9c-b6c5-45e3-b4fd-f08e023133bf
-- title:
--   Finite original-row Farkas certificates prove an exact segment Minkowski summand
-- statement:
--   Let a finite family of linear inequalities describe a set P. Fix a direction g and a nonnegative segment length τ. For every pair consisting of one row increasing along g and one row decreasing along g, suppose a nonnegative linear combination of the original inequalities certifies that the corresponding full g-fiber width is at least τ. Then P is exactly the Minkowski sum of its endpoint erosion by the segment [0,τg] and that segment. This proves a global decomposition equality from finite original-row certificates; it is stronger than merely showing that the erosion is nonempty or that the segment fits at selected points.
-- source:
--   Standalone proof extracted from PR #210 segment-peeling work: https://github.com/jjoshua2/prove2me-work/blob/formal/dual-wall-carrier-routing/research/publication_packets/pr210_catchup/segment_farkas_equality/solution.lean

import Mathlib
open Set
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace HirschSegmentPeelingPublic
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {ι : Type*} [Fintype ι]
def halfspaces (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) : Set E := {x | ∀ i, a i x ≤ b i}
def erosion (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g : E) (τ : ℝ) : Set E := halfspaces a (fun i => b i - τ * max (a i g) 0)
def segmentSum (P : Set E) (g : E) (τ : ℝ) : Set E := {x | ∃ p ∈ P, ∃ t : ℝ, 0 ≤ t ∧ t ≤ τ ∧ x = p + t • g}
structure PairCertificate (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g : E) (τ : ℝ) (i j : ι) where
  weights : ι → ℝ
  nonnegative : ∀ k, 0 ≤ weights k
  normal_identity : ∑ k, weights k • a k = (-a j g) • a i + (a i g) • a j
  constant_bound : (∑ k, weights k*b k) ≤ (-a j g)*b i + (a i g)*b j - τ*(a i g)*(-a j g)
end HirschSegmentPeelingPublic
end

theorem Hirsch.segment_summand_equality_of_farkas_certificates
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g : E) (τ : ℝ)
    (hτ : 0 ≤ τ) (hplus : ∃ i, 0 < a i g)
    (cert : ∀ i j, 0 < a i g → a j g < 0 →
      HirschSegmentPeelingPublic.PairCertificate a b g τ i j) :
    HirschSegmentPeelingPublic.halfspaces a b =
      HirschSegmentPeelingPublic.segmentSum
        (HirschSegmentPeelingPublic.erosion a b g τ) g τ := by sorry
