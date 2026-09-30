-- Prove2me | Theorems.Thm_Hirsch_cut_vertex_selected_active_square_system
-- name    : Hirsch.cut_vertex_selected_active_square_system
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-17T19:46:51.626688+00:00
-- url     : https://prove2.me/theorems/d01a7a03-fda5-4dd3-a058-7f38127c3228
-- title:
--   Construct a mass-preserving square active-row system at every cut vertex
-- statement:
--   For any actual extreme point x of convexHull(S) intersected with m original linear halfspaces in real dimension d, construct a finite positive independent support v_i in S, with n<=d+1 and positive barycentric weights w_i representing x. Select a finite set J of original cuts active at x with exactly n-1 members. The total-mass equation and these selected active-value equations form a square bijective linear system: for EVERY real prescribed mass and EVERY real vector of selected values there exists exactly one real weight vector realizing them. In particular mass one and the original selected right sides uniquely recover w, even among signed alternatives. Neither the support, its weights, selected rows, an inverse, a determinant or a rank oracle is assumed. S need not be finite, closed or compact; support points may individually violate the cuts. The singleton-support case selects no active rows. Existence and exact recovery are proved, not a particular executable row-selection algorithm or a polynomial global catalogue size. This is a finite geometric-algebraic interface, not Polynomial Hirsch.
-- source:
--   Reuses accepted #291 cut_vertex_positive_support proof at64b73e31cdf368e36e6bd76f1710f4fc97760ebb (theorem1043e661-f761-4ee3-9d75-2822a58c77f9); the complete source is unchanged except its top-level theorem/print name. New mass-preserving row extraction uses Mathlib exists_linearIndepOn_extension and finite-dimensional rank arguments. This closes the explicit next row-selection obligation in #291 accepted-evidence.md atc869bba4af34e6912d043293bff128edc4717801. Classical basis extension and barycentric geometry are credited; no historical-priority claim.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.cut_vertex_selected_active_square_system
    (m d : ℕ) (S : Set (Fin d → ℝ))
    (C : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (x : Fin d → ℝ)
    (hx : x ∈ (convexHull ℝ S ∩ {y | ∀ j, C j y ≤ b j}).extremePoints ℝ) :
    ∃ (n : ℕ) (v : Fin n → Fin d → ℝ) (w : Fin n → ℝ)
      (J : Finset {j : Fin m // C j x = b j}),
      (∀ i, v i ∈ S) ∧ (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
      (∑ i, w i • v i) = x ∧
      LinearIndependent ℝ (fun i => ((1 : ℝ), v i)) ∧
      n ≤ d + 1 ∧ J.card + 1 = n ∧
      (∀ (mass : ℝ) (values : J → ℝ), ∃! u : Fin n → ℝ,
        (∑ i, u i) = mass ∧
          ∀ j : J, (∑ i, u i * C j.val.val (v i)) = values j) ∧
      (∀ u : Fin n → ℝ, (∑ i, u i) = 1 →
        (∀ j : J, (∑ i, u i * C j.val.val (v i)) = b j.val.val) → u = w) := by sorry
