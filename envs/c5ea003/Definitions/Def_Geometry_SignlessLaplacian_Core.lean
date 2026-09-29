-- Prove2me | Definitions.Def_Geometry_SignlessLaplacian_Core
-- name    : Geometry_SignlessLaplacian_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:55:33.382667+00:00
-- url     : https://prove2.me/theorems/169526ac-a50b-455a-9b00-a1fa1112700a
-- title:
--   Aether Catalog definitions — Geometry_SignlessLaplacian_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.SignlessLaplacian.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/SignlessLaplacian/Core.lean by skeleton subtraction
import Mathlib
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

namespace SignlessLaplacian

variable {R F : Type*} [Fintype R] [DecidableEq R] [Fintype F]

/-- The signless Laplacian quadratic form `xᵀ (B Bᵀ) x` of the incidence
    structure, written as a manifest sum of squares over the facets. -/
def slQuad (facet : F → Finset R) (x : R → ℝ) : ℝ :=
  ∑ f, (∑ r ∈ facet f, x r) ^ 2

/-- The signless Laplacian matrix entry `L r r'`: the number of facets that
    contain both ridges `r` and `r'`.  (`L = B Bᵀ`.) -/
def slMatrix (facet : F → Finset R) (r r' : R) : ℕ :=
  (Finset.univ.filter (fun f => r ∈ facet f ∧ r' ∈ facet f)).card

/-- The degree of a ridge: the number of facets containing it. -/
def degree (facet : F → Finset R) (r : R) : ℕ :=
  (Finset.univ.filter (fun f => r ∈ facet f)).card

/-- The signless Laplacian spectral radius: the supremum of the Rayleigh
    quotient over nonzero vectors. -/
noncomputable def specRad (facet : F → Finset R) : ℝ :=
  sSup ((fun x : R → ℝ => slQuad facet x / ∑ r, (x r) ^ 2) ''
    {x | (∑ r, (x r) ^ 2) ≠ 0})

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

/-
`0 ≤ specRad`.
-/

/-
The signless Laplacian spectral radius bound: for a structure with facet
    sizes `≤ s` and ridge degrees `≤ D`, the spectral radius is `≤ s·D`.
    For a pure `r`-complex `s = r+1`, giving `q_{r-1}(K) ≤ (r+1)·Δ`.
-/

end SignlessLaplacian


