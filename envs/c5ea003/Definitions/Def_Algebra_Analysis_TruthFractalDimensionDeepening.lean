-- Prove2me | Definitions.Def_Algebra_Analysis_TruthFractalDimensionDeepening
-- name    : Algebra_Analysis_TruthFractalDimensionDeepening
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:05:33.425091+00:00
-- url     : https://prove2.me/theorems/ac2e7da7-a99f-4fcc-a200-38ecb273a3c3
-- title:
--   Aether Catalog definitions — Algebra_Analysis_TruthFractalDimensionDeepening
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.Analysis.TruthFractalDimensionDeepening`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/Analysis/TruthFractalDimensionDeepening.lean by skeleton subtraction
import Mathlib

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

namespace TruthFractalDimensionDeepening

/-- A **theory** assigns to each length `n` the finite set of accepted binary
strings (statements) of that length. -/
abbrev Theory := (n : ℕ) → Finset (Fin n → Bool)

/-- The number of statements of length `n` accepted by a theory. -/
def count (T : Theory) (n : ℕ) : ℕ := (T n).card

/-- The finite-scale dimension estimate: `log₂ (count T n) / n`. -/
noncomputable def dimEstimate (T : Theory) (n : ℕ) : ℝ :=
  Real.logb 2 (count T n) / n

/-- The **box-counting (fractal) dimension** of a theory. -/
noncomputable def boxDim (T : Theory) : ℝ := limsup (dimEstimate T) atTop

/-! ### Universal bounds -/









/-! ### Monotonicity of fractal dimension -/




/-! ### Periodic density theories: realizing every rational dimension -/

/-- The **periodic density theory** with modulus `m` and admissible residues `R`:
a coordinate `i` is free (may be `true` or `false`) exactly when `i mod m ∈ R`;
otherwise it is forced to `false`.  The asymptotic density of free coordinates is
`R.card / m`. -/
noncomputable def densityTheory (m : ℕ) (R : Finset ℕ) : Theory := fun n =>
  Fintype.piFinset (fun i : Fin n =>
    if (i : ℕ) % m ∈ R then (Finset.univ : Finset Bool) else {false})

/-- The number of admissible (free) indices below `n`. -/
def freeCount (m : ℕ) (R : Finset ℕ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun i => i % m ∈ R)).card











/-! ### The dimension spectrum of truth is the whole rational unit interval -/


/-! ### Recovering the extreme and half-information cases as instances

The three landmark values `0`, `1/2`, `1` of the base development are all special
cases of the density law, obtained by tuning `(m, R)`:

* `m = 1`, `R = {0}`  frees every coordinate: dimension `1` (the full space).
* `m = 2`, `R = {0}`  frees the even coordinates: dimension `1/2`.
* `m = 1`, `R = ∅`     frees nothing: dimension `0` (a single string per length).
-/




/-! ### Examples, generalizations, and boundaries (PEGB)

**Examples.**  The concrete instantiations below exhibit the density law at the
three landmark dimensions and check the counting engine on small inputs. -/

-- The free-coordinate count of the "even" theory on the first `6` lengths:
-- `2·⌈n/2⌉`-style growth `0,1,1,2,2,3`.
-- Free-coordinate counts of the density-`1/3` theory (modulus `3`, one residue):
-- `0,1,1,1,2,2,2,3,3` — asymptotic slope `1/3`.
-- The counting law `count = 2 ^ freeCount` at length `4` for the even theory:
-- `2 ^ freeCount 2 {0} 4 = 2 ^ 2 = 4`.
/-!
**Generalization.**  `boxDim_densityTheory` is the broad statement: it computes
the dimension of *every* periodic density theory as the asymptotic density
`R.card / m` of information-bearing coordinates, and `rational_dimension_realized`
turns this into a surjectivity statement onto `[0,1] ∩ ℚ`.  A natural further
generalization replaces the exactly-periodic pattern by any coordinate set of
Dirichlet density `d`; the same squeeze then yields dimension `d`, extending the
realizable spectrum to all densities that are approximable from finite windows.

**Boundary.**  The construction is tight at both ends: `boxDim_full` (`R` full)
and `boxDim_empty` (`R` empty) show the bounds `0 ≤ boxDim ≤ 1` are attained, so
no strictly sharper universal bound exists.  The boundary case that genuinely
requires the `limsup` (rather than an honest limit) is an *aperiodic* theory
whose free-coordinate density oscillates: there the finite estimates do not
converge, only the `limsup` is stable — which is precisely why `boxDim` is
defined as a `limsup` and not a `lim`.
-/

end TruthFractalDimensionDeepening


