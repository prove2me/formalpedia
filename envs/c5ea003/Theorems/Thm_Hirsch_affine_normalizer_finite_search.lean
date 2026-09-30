-- Prove2me | Theorems.Thm_Hirsch_affine_normalizer_finite_search
-- name    : Hirsch.affine_normalizer_finite_search
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-22T19:28:52.595902+00:00
-- url     : https://prove2.me/theorems/e3e924a7-cae1-4fff-9bdb-1433126cb7f7
-- title:
--   Complete finite linear synthesis of optimal positive affine normalizers
-- statement:
--   For an arbitrary finite set C in real ambient dimension d, arbitrary scalar numerator data s, and anchor u in C, construct one positive anchored affine denominator for each subset of C x C of size at most d. Whenever that subset's explicit ratio-coincidence linear equations admit a positive solution, the chosen member satisfies them. Every positive affine denominator with arbitrary real coefficients has all of its ratio coincidences preserved by some catalogue member, whose spectrum cardinality is therefore no greater. A single catalogue member minimizes the spectrum cardinality over ALL positive affine denominators. No denominator, partition, independent basis, rank, small spectrum or short route is an input. Signed and zero numerators, nonspanning/lower-dimensional C, dimension zero and arbitrarily small positive denominators are included. This is finite mathematical existence/completeness, not a Lean-extracted LP solver, a polynomial original-facet algorithm or a uniform Polynomial Hirsch bound. Original-edge applications use the separately accepted #333 theorem and require a complete actual vertex set and original H/hull equality.
-- source:
--   Classical finite-dimensional span compression and strict linear feasibility. Normalize the denominator at u, linearize each ratio equality in its d slope variables, derive at most d original contrast equations spanning every tie, and select a positive feasible solution per finite subsystem. Difference-of-solutions kernel reasoning preserves all old ties; finite-image coarsening and finite minimization yield an optimum over every real positive affine denominator. This addresses #333's separate denominator-choice gap, unlike #204's product-chart discovery. No historical-priority, universally binary spectrum or efficient H-to-V claim. No prior accepted target is imported or resubmitted.

import Mathlib
set_option autoImplicit false

theorem Hirsch.affine_normalizer_finite_search (d : ℕ) (C : Finset (Fin d → ℝ))
    (s : (Fin d → ℝ) → ℝ) (u : Fin d → ℝ) (hu : u ∈ C) :
    let F := (C.product C).powerset.filter (fun B => B.card ≤ d)
    ∃ pick : F → ((Fin d → ℝ) →ₗ[ℝ] ℝ),
      (∀ B, ∀ x ∈ C, 0 < 1+pick B (x-u)) ∧
      (∀ B, (∃ D : (Fin d → ℝ) →ₗ[ℝ] ℝ,
        (∀ x ∈ C, 0 < 1+D (x-u)) ∧
          ∀ p ∈ B.val, D (s p.1 • (p.2-u)-s p.2 • (p.1-u))=s p.2-s p.1) →
        ∀ p ∈ B.val, pick B (s p.1 • (p.2-u)-s p.2 • (p.1-u))=s p.2-s p.1) ∧
      (∀ a : ℝ, ∀ D : (Fin d → ℝ) →ₗ[ℝ] ℝ,
        (∀ x ∈ C, 0 < a+D x) → ∃ B : F,
          (∀ x ∈ C, ∀ y ∈ C, s x/(a+D x)=s y/(a+D y) →
            s x/(1+pick B (x-u))=s y/(1+pick B (y-u))) ∧
          (C.image (fun x => s x/(1+pick B (x-u)))).card ≤
            (C.image (fun x => s x/(a+D x))).card) ∧
      ∃ B : F, ∀ a : ℝ, ∀ D : (Fin d → ℝ) →ₗ[ℝ] ℝ,
        (∀ x ∈ C, 0 < a+D x) →
          (C.image (fun x => s x/(1+pick B (x-u)))).card ≤
            (C.image (fun x => s x/(a+D x))).card := by sorry
