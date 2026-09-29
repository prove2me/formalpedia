-- Prove2me | solution 1 for SignlessLaplacian.slQuad_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:55:37.753064+00:00
-- url     : https://prove2.me/submissions/71094023-b495-4cdd-997a-46494af08a47

-- Sol generated from Geometry/SignlessLaplacian/Core.lean
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
theorem sum_facet_eq_degree (facet : F → Finset R) (g : R → ℝ) :
    ∑ f, ∑ r ∈ facet f, g r = ∑ r, (degree facet r : ℝ) * g r := by
  -- By definition of degree, we can rewrite the inner sum as a sum over all ridges r.
  have h_inner : ∀ r, ∑ f ∈ Finset.univ, (if r ∈ facet f then g r else 0) = (degree facet r : ℝ) * g r := by
    simp +decide [ Finset.sum_ite, degree ];
  rw [ ← Finset.sum_congr rfl fun r hr => h_inner r, Finset.sum_comm ];
  simp +decide

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


open SignlessLaplacian in
theorem solution(facet : F → Finset R) (x : R → ℝ) (s D : ℕ)
    (hs : ∀ f, (facet f).card ≤ s) (hD : ∀ r, degree facet r ≤ D) :
    slQuad facet x ≤ (s * D : ℝ) * ∑ r, (x r) ^ 2 := by
  -- By the given conditions, we can bound each facet term by `s * ∑ r ∈ facet f, (x r)^2`.
  have slQuad_bound (f : F) : (∑ r ∈ facet f, x r) ^ 2 ≤ s * ∑ r ∈ facet f, (x r) ^ 2 := by
    -- Apply the Cauchy-Schwarz inequality to the sum over the facet f.
    have h_cauchy_schwarz : (∑ r ∈ facet f, x r) ^ 2 ≤ (Finset.card (facet f)) * (∑ r ∈ facet f, (x r) ^ 2) := by
      exact sq_sum_le_card_mul_sum_sq
    exact h_cauchy_schwarz.trans ( mul_le_mul_of_nonneg_right ( mod_cast hs f ) ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) );
  -- Summing over all facets, we get `slQuad facet x ≤ s * ∑ f, ∑ r ∈ facet f, (x r)^2`.
  have slQuad_sum_bound : slQuad facet x ≤ s * ∑ f, ∑ r ∈ facet f, (x r) ^ 2 := by
    simpa only [ Finset.mul_sum _ _ _ ] using Finset.sum_le_sum fun f _ => slQuad_bound f;
  -- Applying the already-proven lemma `sum_facet_eq_degree` with `g r = (x r)^2`, we get `∑ f, ∑ r ∈ facet f, (x r)^2 = ∑ r, (degree facet r : ℝ) * (x r)^2`.
  have sum_facet_eq_degree_x2 : ∑ f, ∑ r ∈ facet f, (x r) ^ 2 = ∑ r, (degree facet r : ℝ) * (x r) ^ 2 := by
    convert sum_facet_eq_degree facet ( fun r => x r ^ 2 ) using 1;
  rw [ mul_assoc ];
  exact slQuad_sum_bound.trans ( mul_le_mul_of_nonneg_left ( by rw [ sum_facet_eq_degree_x2, Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ( mod_cast hD i ) ( sq_nonneg _ ) ) ( Nat.cast_nonneg _ ) )
