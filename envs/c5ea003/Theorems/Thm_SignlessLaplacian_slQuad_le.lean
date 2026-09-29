-- Prove2me | Theorems.Thm_SignlessLaplacian_slQuad_le
-- name    : SignlessLaplacian.slQuad_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:50:17.653852+00:00
-- url     : https://prove2.me/theorems/f6669a9b-bce1-4219-bb0b-0d3758c960fa
-- title:
--   SlQuad le
-- statement:
--   Formal statement of `SignlessLaplacian.slQuad_le` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem SignlessLaplacian.slQuad_le(facet : F → Finset R) (x : R → ℝ) (s D : ℕ)
--       (hs : ∀ f, (facet f).card ≤ s) (hD : ∀ r, degree facet r ≤ D) :
--       slQuad facet x ≤ (s * D : ℝ) * ∑ r, (x r) ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/SignlessLaplacian/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/SignlessLaplacian/Core.lean#L122

-- Thm stub generated from Geometry/SignlessLaplacian/Core.lean
import Mathlib
import Definitions.Def_Geometry_SignlessLaplacian_Core
/-
  Signless Laplacian spectral radius of pure simplicial complexes
  ===============================================================

  This file develops the analytic core behind the conjecture of
  arXiv:2303.04252 / doi:10.1016/j.disc.2023.112345 on the signless
  Laplacian spectral radius `q_{r-1}(K)` of a pure `r`-dimensional
  simplicial complex.

  We model the *facet–ridge incidence* of a pure `r`-dimensional complex
  abstractly: the `(r-1)`-faces (called *ridges*) are indexed by `R`, and
  each `r`-face (*facet*) is a finite set of ridges `facet f : Finset R`.
  (For a pure `r`-complex every facet contains exactly `r+1` ridges.)

  The *signless Laplacian* on the ridges is the matrix `L = B Bᵀ` where `B`
  is the unsigned ridge–facet incidence matrix.  Its associated quadratic
  form is the manifest sum of squares

      `slQuad facet x = ∑ f, (∑ r ∈ facet f, x r)^2`,

  and the *signless Laplacian spectral radius* is the supremum of the
  Rayleigh quotient `slQuad facet x / ‖x‖²`.  (For the Hermitian positive
  semidefinite matrix `L` this Rayleigh supremum equals the largest
  eigenvalue, i.e. the usual spectral radius `q_{r-1}`.)

  Main results (all fully proved, 0 sorries):
  * `slQuad_nonneg`         : the form is positive semidefinite;
  * `slQuad_eq_matrix`      : it really is `xᵀ L x` for the signless Laplacian;
  * `slQuad_le`             : the Cauchy–Schwarz / row–sum bound
                              `slQuad ≤ (facet size)·(max degree)·‖x‖²`;
  * `specRad_le`            : hence `q ≤ (r+1)·Δ` for a pure `r`-complex;
  * `specRad_nonneg`        : `q ≥ 0`;
  * `simplex_specRad`       : sharpness — a single `r`-simplex attains `q = r+1`.

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): The signless Laplacian spectral radius of a
    pure complex is governed by `(facet size) × (max ridge degree)`, the
    higher-dimensional analogue of the graph bound `q(G) ≤ 2Δ`.  The
    homology-vanishing hypothesis of the conjecture is, in this language, a
    device for bounding the ridge degrees.
  Experiment (Experimenter): formalize the incidence model, prove the
    sum-of-squares identity, the matrix identity, and the Cauchy–Schwarz
    facet-wise bound, then assemble the Rayleigh-quotient spectral bound.
  Analysis (Analyst): the per-facet Cauchy–Schwarz inequality
    `(∑_{r∈f} x_r)² ≤ |f| ∑_{r∈f} x_r²` is the crux; summing and
    double-counting turns `∑_f |f| ∑_{r∈f} x_r²` into `∑_r deg(r) x_r²`.
  Critique (Critic): `specRad` is defined as a genuine supremum of Rayleigh
    quotients, NOT as the trivially-bounded form; sharpness is exhibited by
    an explicit simplex, so the bound is not vacuous.
  Synthesis (PI): a reusable, dimension-free engine for signless Laplacian
    spectral bounds of simplicial complexes; see `FUTURE_DIRECTIONS.md`.
-/

open Finset BigOperators

open SignlessLaplacian

variable {R F : Type*} [Fintype R] [DecidableEq R] [Fintype F]





/-
The signless Laplacian quadratic form is positive semidefinite.
-/

/-
The sum-of-squares form really is `xᵀ L x` for the signless Laplacian
    matrix `L = B Bᵀ`.
-/

/-
Double counting: summing a ridge function over all facets weights each
    ridge by its degree.
-/

/-
The Cauchy–Schwarz / row-sum bound for the signless Laplacian quadratic
    form: if every facet has at most `s` ridges and every ridge lies in at
    most `D` facets, then `slQuad ≤ s·D·‖x‖²`.
-/

theorem SignlessLaplacian.slQuad_le(facet : F → Finset R) (x : R → ℝ) (s D : ℕ)
    (hs : ∀ f, (facet f).card ≤ s) (hD : ∀ r, degree facet r ≤ D) :
    slQuad facet x ≤ (s * D : ℝ) * ∑ r, (x r) ^ 2 := by sorry
