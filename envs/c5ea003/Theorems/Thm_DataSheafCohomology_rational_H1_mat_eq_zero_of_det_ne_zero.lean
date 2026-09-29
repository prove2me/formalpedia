-- Prove2me | Theorems.Thm_DataSheafCohomology_rational_H1_mat_eq_zero_of_det_ne_zero
-- name    : DataSheafCohomology.rational_H1_mat_eq_zero_of_det_ne_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:29:48.587775+00:00
-- url     : https://prove2.me/theorems/48aa1373-6bb3-4dbd-9765-1d3299220f7f
-- title:
--   A nonzero determinant makes the rational obstruction vanish identically.
-- statement:
--   A nonzero determinant makes the rational obstruction vanish identically.
--
--   ```lean
--   theorem DataSheafCohomology.rational_H1_mat_eq_zero_of_det_ne_zero(M : Matrix (Fin n) (Fin n) ℤ)
--       (h : M.det ≠ 0) :
--       finrank ℚ ((Fin n → ℚ) ⧸ LinearMap.range (M.map (Int.cast : ℤ → ℚ)).mulVecLin) = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/DataSheafCohomology.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/DataSheafCohomology.lean#L784

-- Thm stub generated from Algebra/DataSheafCohomology.lean
import Mathlib
import Definitions.Def_Algebra_DataSheafCohomology
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Restriction Ranks, Holonomy, and the First Cohomology of Data Nerves

This module continues the *Sheaf Cohomology of Data* thread.  The previous cycle
(`Catalog/MachineLearning/SheafCohomologyRobustness/Cohomology.lean`) treated the
**constant** sheaf on a path nerve and on a cyclic nerve, with scalar stalks and
identity restriction maps, and showed `H¹(path) = 0`, `H¹(cycle) ≠ 0`.

The present file removes both restrictions of that analysis.  Restriction maps
are now arbitrary linear maps, stalks are arbitrary finite dimensional vector
spaces over an arbitrary field, and the nerve is allowed to carry `2`-cells.
The theme is the *Future Directions* claim of the thread:

> a scalar missing rate and a feature count do not determine `H¹`; the
> restriction-map ranks and the overlap incidence are what matter.

We make this precise and prove it.

## Main results

* `finrank_H1_add_finrank_range` and `euler_characteristic` — the exact
  rank–nullity ledger of a two-term data complex.
* `finrank_H1_eq_finrank_ker` — for equidimensional complexes, the obstruction
  dimension equals the dimension of the space of global sections.
* `H1_pos_of_finrank_lt` — a purely numerical certificate for a nonzero
  obstruction.
* `finrank_H1full_add_finrank_range` and `finrank_H1full_le_finrank_H1` — adding
  the `2`-cells of the nerve can only shrink `H¹`.
* `flag_reduction_fails` — **a counterexample to the pairwise (clique/flag)
  reduction conjecture**: on the triangle nerve with constant stalks the
  `1`-skeleton computes `dim H¹ = 1` while the full nerve computes `dim H¹ = 0`.
* `cyclic_holonomy_criterion` — **monodromy law**: for a cyclic nerve with
  invertible scalar restriction maps `a₀, …, a_m`, `H¹ = 0` iff the holonomy
  `∏ aⱼ ≠ 1`, and `dim H¹ = 1` otherwise.  The overlap incidence is fixed
  throughout; only the *values* of the restriction maps move the cohomology.
* `finrank_H1_disjointLoops` — **exact rank law for the disjoint-loop nerve**:
  `dim H¹ = #{i | aᵢ = 1}`, an arbitrary integer in `[0, N]`.
* `missing_rate_does_not_determine_H1` — the headline corollary: for every
  feature count `N` and every target `k ≤ N` there is a data sheaf with
  *invertible* restriction maps on one and the same overlap nerve whose
  obstruction dimension is exactly `k`.  Hence no function of (feature count,
  missing rate, overlap incidence) can predict `dim H¹`.
* `integral_H1_torsion` and `torsion_obstruction_invisible_to_field_coefficients`
  — **the torsion barrier**: over `ℤ` the same data sheaf can carry a nonzero
  (pure torsion) obstruction while its field-coefficient obstruction vanishes
  identically.  Field-valued cohomology, the only kind computed in practice, is
  therefore not a complete gluing invariant.
* `det_smul_H1Zmat_eq_zero` and `integral_vs_rational_dichotomy` — the universal
  form of the barrier: for an arbitrary square integer coboundary `M`, `det M`
  annihilates the integral obstruction, and if `det M ≠ 0` the rational
  obstruction vanishes identically.

-- !-- Lab Notes -- !--
* Hypothesis (Hypothesizer).  Bold conjecture C2 of the thread: *`dim H¹` is not
  a function of the missingness marginals.*  Bold conjecture C3: *the flag /
  pairwise-clique nerve computes the same `H¹` as the full nerve.*  Bold
  conjecture C1: *`dim H¹ / dim C¹` is governed by a rank law.*
* Experiment (Experimenter).  C3 was attacked first because it is the cheapest
  to refute.  The triangle nerve with constant stalks was computed by hand:
  `dim C⁰ = dim C¹ = 3`, `dim ker δ⁰ = 1` (the constants), so `rank δ⁰ = 2` and
  the skeleton gives `dim H¹ = 3 - 2 = 1`; but `range δ⁰ = ker δ¹` exactly, so
  the full nerve gives `dim H¹ = 0`.  Formalised as `flag_reduction_fails`:
  **C3 is false**.
* Experiment (Experimenter).  C1 was replaced by an exact deterministic rank law
  in two model families where it can be computed in closed form: the cyclic
  nerve (`cyclic_holonomy_criterion`, a discrete monodromy statement — the
  kernel is a parallel-transport orbit, `ker_transport`) and the disjoint-loop
  nerve (`finrank_H1_disjointLoops`, where `dim H¹` counts the loops with
  trivial holonomy).  Both confirm the *shape* of C1: the normalized dimension
  is a function of the restriction data, not of the incidence alone.
* Analysis (Analyst).  The two families separate the two possible causes of
  obstruction.  On the cycle the obstruction is *global* (one scalar holonomy,
  `dim H¹ ≤ 1` no matter how many features).  On the disjoint loops it is
  *local and additive* (`dim H¹` grows linearly in the feature count).  This is
  the structural reason why a scalar missing rate cannot predict `dim H¹`: the
  same rate is compatible with a globally rigid nerve and with a maximally
  fragmented one.  Failure classification: C3 = **false**; C2 = **true and now
  proved**; C1 = **true but needs a different definition** (the deterministic
  limit exists only after conditioning on the restriction-rank profile).
* Critique (Critic).  Is `missing_rate_does_not_determine_H1` cheating by using
  zero restriction maps?  No: the hypothesis `∀ i, a i ≠ 0` forces every
  restriction map in the construction to be an *isomorphism* of stalks, so the
  separation is not a rank degeneracy — it is pure holonomy.  Is
  `flag_reduction_fails` an artifact of a degenerate nerve?  No: the triangle is
  the smallest flag nerve, its restriction maps are identities, and both
  cohomologies are computed exactly rather than bounded.
* Synthesis (PI).  `dim H¹` is the corank of the transport system.  Incidence
  fixes the *shape* of the ledger; the restriction maps fix its *rank*.
* Second loop — Hypothesis.  If the restriction maps fix the rank, what fixes
  the *arithmetic*?  Conjecture: over `ℤ` the disjoint-loop obstruction is
  `⨁ᵢ ℤ/(aᵢ - 1)`, hence pure torsion whenever no `aᵢ = 1` — exactly the regime
  in which the field-valued theory reports nothing.
* Second loop — Experiment.  `mem_range_loopDZ` identifies the integral
  coboundary image as the coordinatewise divisibility condition
  `(aᵢ - 1) ∣ gᵢ`.  Annihilation by `∏ᵢ(aᵢ - 1)` (`integral_H1_torsion`) and
  nontriviality of the indicator class (`integral_H1_nontrivial_of_not_dvd_one`)
  then give the barrier; `rational_H1_vanishes_of_no_trivial_loop` supplies the
  vanishing field-side comparison.
* Second loop — Critique.  Is the `2`-torsion statement vacuous because the
  module might be zero?  No: the first conjunct of
  `torsion_obstruction_invisible_to_field_coefficients` exhibits a nonzero
  element explicitly, so the module is nonzero and `2`-torsion, i.e. genuinely
  `ℤ/2`.
* Third loop — Synthesis.  The two integral computations are one theorem: the
  adjugate identity `M · adj M = det M · 1` shows that `det M` is a universal
  annihilator of the integral obstruction of any equidimensional data complex,
  and `rational_H1_mat_eq_zero_of_det_ne_zero` shows the field-valued theory is
  blind exactly on the locus `det M ≠ 0` where that annihilator is nontrivial.
  The determinant, not the rank, is the right exponent.
-/


open Module Finset

open DataSheafCohomology

/-! ## §1.  The obstruction space of a two-term data complex

A *data complex* is a linear map `d⁰ : C⁰ → C¹` from the space of local sections
(one stalk per feature block) to the space of overlap discrepancies (one stalk
per overlap).  `H⁰ = ker d⁰` are the globally consistent local sections and
`H¹ = C¹ ⧸ range d⁰` is the obstruction space. -/


variable {K C0 C1 C2 : Type*} [Field K]
  [AddCommGroup C0] [Module K C0] [AddCommGroup C1] [Module K C1]
  [AddCommGroup C2] [Module K C2]








/-! ### The full nerve: adding `2`-cells -/






/-! ## §2.  Counterexample to the pairwise (flag) reduction conjecture

Conjecture C3 of the thread asks whether, for a flag nerve, the clique complex
generated by *pairwise* overlaps computes the same `H¹` as the full nerve.  The
triangle nerve `{U₀, U₁, U₂}` with all pairwise and the triple overlap nonempty
is flag, and refutes it. -/


variable (K : Type*) [Field K]











/-! ## §3.  The cyclic nerve with general invertible restriction maps: holonomy

Feature blocks `U₀, …, U_m` are arranged in a loop, each stalk is the field `K`,
and the restriction map across the overlap `Uᵢ ∩ Uᵢ₊₁` is multiplication by a
scalar `aᵢ`.  The coboundary is `(δf)ᵢ = aᵢ · f(i+1) - f(i)` with `i+1` taken
modulo `m+1`.  The overlap incidence is the *same* cyclic nerve as in the
previous cycle of this thread; only the restriction maps change. -/


variable {K : Type*} [Field K]



variable {m : ℕ}


















/-! ## §4.  The disjoint-loop nerve: an exact rank law, and the failure of any
missing-rate scaling law

Now the nerve consists of `N` feature blocks, each overlapping only itself (a
self-loop: the block is re-observed in a second sample batch).  The restriction
map on loop `i` is multiplication by `aᵢ`; the coboundary is
`(δf)ᵢ = aᵢ · f i - f i`.  Every restriction map is an isomorphism as soon as
`aᵢ ≠ 0`, yet the obstruction dimension is *exactly* the number of loops with
trivial holonomy — an arbitrary integer between `0` and `N`. -/


variable {K : Type*} [Field K] [DecidableEq K] {N : ℕ}










/-! ## §5.  The torsion barrier: integral coefficients see obstructions that no
field sees

Everything above is linear algebra over a field, which is what the applied
literature computes.  Replacing the field by `ℤ` — stalks `ℤ`, restriction maps
integer multiplications — reveals a strictly finer invariant.  On the
disjoint-loop nerve the integral obstruction is `⨁ᵢ ℤ/(aᵢ - 1)`, which is pure
torsion as soon as no `aᵢ` equals `1`; and pure torsion is exactly what becomes
invisible after tensoring with any field of characteristic `0`. -/


variable {N : ℕ}










/-! ## §6.  The determinant is the universal exponent of the integral obstruction

The two integral computations above are instances of one statement.  For *any*
data complex whose coboundary is a square integer matrix `M` — i.e. as many
overlap degrees of freedom as local ones, the equidimensional situation of
`finrank_H1_eq_finrank_ker` — the integral obstruction is annihilated by
`det M`, by the adjugate identity.  When `det M ≠ 0` the field-valued
obstruction vanishes identically, so *everything* the integral theory sees in
that regime is torsion of exponent dividing `|det M|`. -/


open Matrix

variable {n : ℕ}

theorem DataSheafCohomology.rational_H1_mat_eq_zero_of_det_ne_zero(M : Matrix (Fin n) (Fin n) ℤ)
    (h : M.det ≠ 0) :
    finrank ℚ ((Fin n → ℚ) ⧸ LinearMap.range (M.map (Int.cast : ℤ → ℚ)).mulVecLin) = 0 := by sorry
