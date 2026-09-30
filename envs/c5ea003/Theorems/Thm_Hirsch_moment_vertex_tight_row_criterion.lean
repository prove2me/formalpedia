-- Prove2me | Theorems.Thm_Hirsch_moment_vertex_tight_row_criterion
-- name    : Hirsch.moment_vertex_tight_row_criterion
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-17T10:16:36.884203+00:00
-- url     : https://prove2.me/theorems/01977493-8c4e-45c5-957d-236e1d3fd475
-- title:
--   Exact moment vertex criterion and constructive full rank of every tight-row set
-- statement:
--   For every d<m and injective real parameters a on all m original labels, form the original mean-centered moment system row_i(x)<=1 in R^d. At EVERY ambient point x, let I be exactly the original rows tight at x. Prove |I|<=d and construct arbitrary prescribed real values on these active rows: for any values:I->R there exists z with row_i(z)=values_i. Thus active-row evaluation is surjective and the tight rows have full row rank, without a rank or inverse oracle. Finally prove the exact characterization: x is a Mathlib extreme point of the original feasible set if and only if x is feasible and |I|=d. This holds also in dimension zero; no compactness, simplicity, sorted nodes, facet catalogue or extreme-point list is assumed. Polynomial root counting supplies the cardinal bound; Lagrange interpolation plus a centering correction using x supplies the right inverse; finite-margin opposite perturbations characterize extremality by active evaluation injectivity. The theorem is distinct from the separately owned compactness/interior packet and does not prove an original-edge route bound or Polynomial Hirsch.
-- source:
--   Continues the vertex/simplicity interface after accepted moment minimality/catalogue results. Reuses unchanged evaluation helpers from accepted #285/#286 via #287 (source f94f741869ca14b3bea3a506cab5f09083dc54ab) and the finite_margin body from accepted #290 (56e38bebb4d5b3501ee47c05df59631d5c5c0543) under a new helper namespace. The independently prepared compactness packet was withheld when live #292 was found; no compactness duplicate is submitted. Classical interpolation, finite-dimensional rank and polyhedral extremality are credited, with no historical-priority claim.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.moment_vertex_tight_row_criterion (d m : ℕ) (hm : d < m) (a : Fin m → ℝ)
    (ha : Function.Injective a) :
    let row : (Fin d → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin d,
        (a i ^ (j.val+1) - (∑ z, a z ^ (j.val+1)) / (m : ℝ)) * x j
    let P : Set (Fin d → ℝ) := {x | ∀ i, row x i ≤ 1}
    ∀ x : Fin d → ℝ,
      let I : Finset (Fin m) := Finset.univ.filter (fun i => row x i = 1)
      I.card ≤ d ∧
      (∀ values : I → ℝ, ∃ z : Fin d → ℝ, ∀ i : I, row z i.val = values i) ∧
      (x ∈ P.extremePoints ℝ ↔ (∀ i, row x i ≤ 1) ∧ I.card = d) := by sorry
