-- Prove2me | Theorems.Thm_TruthFractalDimensionDeepening_tendsto_dimEstimate_densityTheory
-- name    : TruthFractalDimensionDeepening.tendsto_dimEstimate_densityTheory
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T11:01:04.033604+00:00
-- url     : https://prove2.me/theorems/518bb008-08f4-4a1f-b485-9dabd92e76c7
-- title:
--   The finite estimates of a periodic density theory converge to the density.
-- statement:
--   The finite estimates of a periodic density theory converge to the density.
--
--   ```lean
--   theorem TruthFractalDimensionDeepening.tendsto_dimEstimate_densityTheory(m : ℕ) (R : Finset ℕ) (hR : R ⊆ Finset.range m)
--       (hm : 1 ≤ m) :
--       Tendsto (dimEstimate (densityTheory m R)) atTop (nhds (R.card / m)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/Analysis/TruthFractalDimensionDeepening.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/Analysis/TruthFractalDimensionDeepening.lean#L227

-- Thm stub generated from Algebra/TruthFractalDimensionDeepening.lean
import Mathlib
import Definitions.Def_Algebra_TruthFractalDimensionDeepening

/-!
# The Fractal Dimension of Mathematical Truth — Deepening

This file deepens the study of the box-counting (fractal) dimension of the space
of true statements.  In the base development, statements are encoded as finite
binary strings (a length-`n` statement is a function `Fin n → Bool`), a *theory*
`T` assigns to each length the finite set of accepted strings, and the fractal
dimension is

  `boxDim T = limsup_n  log₂ (count T n) / n`,   `count T n = (T n).card`.

There it was shown that an explicit "half-information" theory has dimension
exactly `1/2`.  Here we prove the sharp *generalization*:

## Main results

* `boxDim_densityTheory`: for every modulus `m ≥ 1` and every set of admissible
  residues `R ⊆ {0,…,m-1}`, the **periodic density theory** — which frees a
  coordinate `i` exactly when `i mod m` is admissible — has fractal dimension
  exactly `R.card / m`, the asymptotic density of free coordinates.
* `rational_dimension_realized`: consequently **every rational number in `[0,1]`
  is the fractal dimension of some theory of truth.**  The dimension spectrum of
  truth is the whole rational unit interval, not the single value `1/2`.
* `boxDim_mono`: fractal dimension is **monotone** under inclusion of theories.
* `boxDim_le_one` / `boxDim_nonneg`: every dimension lies in `[0,1]`.

The engine is an exact two-sided count of free coordinates: writing
`freeCount m R n` for the number of admissible indices below `n`, we prove the
counting law `count = 2 ^ freeCount`, the clean sandwiching
`R.card·⌊n/m⌋ ≤ freeCount ≤ R.card·⌊n/m⌋ + R.card`, and squeeze the ratio to the
density.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the value `1/2` obtained for one particular truth set
is not special; the fractal dimension is exactly the asymptotic density of
"information-bearing" coordinates, so by tuning that density every rational in
`[0,1]` should be attained.  Bold form: the dimension spectrum of truth is a
dense subset of `[0,1]`.

Experiment (Experimenter): we introduced the periodic density theory
`densityTheory m R` (coordinate `i` is free iff `i mod m ∈ R`), proved the exact
count `2 ^ freeCount`, established the periodicity `freeCount (n+m) = freeCount n
+ R.card` via a complete-residue-system bijection, derived the sandwich bounds by
monotonicity, and squeezed the finite estimates to `R.card / m`.

Analysis (Analyst): the argument is robust because it never depends on the
*identity* of the admissible residues, only on their count `R.card`; this is why
the whole rational interval is realized.  The `limsup` collapses to a genuine
limit here because the density theory is asymptotically regular; irregular
theories genuinely need the `limsup`.

Critique (Critic): the results are not definitional — `boxDim_densityTheory`
rests on an exact combinatorial count plus an analytic squeeze, and
`rational_dimension_realized` produces a witness for each target value rather
than asserting existence abstractly.  Monotonicity is proved at the level of
`limsup`, guarding against the corner case `count = 0` (where `log₂ 0 = 0`).

Synthesis (PI): measured by covering the Cantor space of statements, the possible
fractal dimensions of truth fill the rational unit interval, each realized by a
concrete periodic theory whose free-coordinate density equals the dimension.
-/

open Filter Topology

open TruthFractalDimensionDeepening





/-! ### Universal bounds -/









/-! ### Monotonicity of fractal dimension -/




/-! ### Periodic density theories: realizing every rational dimension -/

theorem TruthFractalDimensionDeepening.tendsto_dimEstimate_densityTheory(m : ℕ) (R : Finset ℕ) (hR : R ⊆ Finset.range m)
    (hm : 1 ≤ m) :
    Tendsto (dimEstimate (densityTheory m R)) atTop (nhds (R.card / m)) := by sorry
