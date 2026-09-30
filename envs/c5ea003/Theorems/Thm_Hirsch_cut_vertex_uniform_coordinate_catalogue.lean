-- Prove2me | Theorems.Thm_Hirsch_cut_vertex_uniform_coordinate_catalogue
-- name    : Hirsch.cut_vertex_uniform_coordinate_catalogue
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-17T20:02:01.161376+00:00
-- url     : https://prove2.me/theorems/f7bdc6f6-ecfb-4525-816e-7e66d0ae6ad3
-- title:
--   One finite cut-image recipe catalogue covers every cut-vertex coordinate
-- statement:
--   Let S be any generating set in real d-dimensional coordinate space, C a finite family of m linear cuts with right-hand side b, Omega a finite set containing the whole m-component cut image of every point of S, and Lambda a finite set containing every coordinate of every point of S. There exists ONE finite scalar set K containing every coordinate of EVERY extreme point of convexHull(S) intersected with those halfspaces. Its cardinality is at most sum from n=0 to min(d+1,m+1) of 2^m times |Omega|^n times |Lambda|^n. Neither cut vertices, positive supports, their weights, an active-row choice, a catalogue, nor catalogue membership are supplied. The proof constructs all finite active-mask, cut-image-tuple and scalar-tuple recipes and decodes one scalar per recipe, using the accepted support-selection/unique-weight theorem to show every actual coordinate is decoded. Inconsistent recipes may output zero; underdetermined recipes may select arbitrary solutions, so K is an overcover, not an exact attained-value list. The empty-support term is harmless padding in the count. The coefficient recipe uses classical choice, not a certified executable solver. The bound is not polynomial in unrestricted cut count and does not establish Polynomial Hirsch.
-- source:
--   Uses accepted PR #291 Hirsch.cut_vertex_positive_support_certificate, theorem1043e661-f761-4ee3-9d75-2822a58c77f9, submissionac775547-35a3-498c-ab38-ad117c2a4d11. Its complete solution is reused with only the top-level declaration/print name changed to accepted_positive_support. New work constructs one globally shared finite scalar catalogue via bounded positive-support sizes, active masks, finite images, unique coefficient recovery and finite-type counting. This is distinct from the concurrently owned #294 sharper square-row extraction. Classical convex geometry and finite enumeration; no historical novelty or uniform arbitrary-carrier inventory claim.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.cut_vertex_uniform_coordinate_catalogue
    (m d : ℕ) (S : Set (Fin d → ℝ))
    (C : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (Ω : Finset (Fin m → ℝ)) (Λ : Finset ℝ)
    (hΩ : ∀ v ∈ S, (fun j => C j v) ∈ Ω)
    (hΛ : ∀ v ∈ S, ∀ k, v k ∈ Λ) :
    ∃ K : Finset ℝ,
      K.card ≤ ∑ n : Fin (min (d + 1) (m + 1) + 1),
        2 ^ m * Ω.card ^ n.val * Λ.card ^ n.val ∧
      ∀ x : Fin d → ℝ,
        x ∈ (convexHull ℝ S ∩ {y | ∀ j, C j y ≤ b j}).extremePoints ℝ →
        ∀ k, x k ∈ K := by sorry
