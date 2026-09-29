-- Prove2me | Definitions.Def_Novelty_Wasserstein
-- name    : Novelty_Wasserstein
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:50:36.800994+00:00
-- url     : https://prove2.me/theorems/6146a2e8-09c9-456a-adb2-197c831fd029
-- title:
--   Aether Catalog definitions — Novelty_Wasserstein
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Wasserstein`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Wasserstein.lean by skeleton subtraction
import Mathlib

/-!
# Finite Wasserstein distance and its metric axioms

This file defines the (finite) optimal-transport value
`wValue d a b = ⨅ { transportCost d π | π a plan between a and b }`
of a *ground cost* `d` between two mass distributions `a, b` on `Fin n`, and proves
the metric-style axioms of the associated Wasserstein distance:

* `wValue_nonneg` — nonnegativity (for a nonnegative ground cost);
* `wValue_self` — `wValue d a a = 0` when the ground cost vanishes on the diagonal;
* `wValue_symm` — symmetry, when the ground cost is symmetric.

It re-states the Kantorovich primitives (`IsTransportPlan`, `transportCost`,
`feasibleSet`) of `Novelty.OptimalTransport.Kantorovich` so that the file is
self-contained; the development is the square (`n = m`) case of that file.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the optimal-transport value of a metric ground cost
should itself be a (pseudo)metric on distributions — the Wasserstein distance.
Experiment (Experimenter): define `wValue` as an `sInf` of the cost image and prove
nonnegativity, self-distance zero (via the diagonal coupling), and symmetry (via the
transpose coupling).  Analysis (Analyst): nonnegativity and symmetry are "soft" and
need only order/bijection arguments; the diagonal coupling makes `wValue d a a = 0`
because its cost is `∑ a i * d i i = 0`.  The triangle inequality is the genuinely
hard axiom (gluing lemma with division by the middle marginal) and is recorded as a
future direction.  Critique (Critic): we require `d ≥ 0` for nonnegativity and the
sInf to be well-behaved; without it the value can be negative and the "distance"
interpretation fails, so the hypothesis is correctly guarded.
-- !-- end Lab Notes -- !--
-/

namespace Novelty.OptimalTransport

open scoped BigOperators
open Set

variable {n : ℕ}

/-- `π` is a transport plan (coupling) between distributions `a` and `b` on `Fin n`:
entrywise nonnegative, with row marginals `a` and column marginals `b`. -/
def IsTransportPlan (a b : Fin n → ℝ) (π : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ π i j) ∧ (∀ i, ∑ j, π i j = a i) ∧ (∀ j, ∑ i, π i j = b j)

/-- Total transport cost of plan `π` against ground cost `d`. -/
def transportCost (d : Fin n → Fin n → ℝ) (π : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, π i j * d i j

/-- Feasible set of couplings between `a` and `b`. -/
def feasibleSet (a b : Fin n → ℝ) : Set (Fin n → Fin n → ℝ) :=
  {π | IsTransportPlan a b π}

/-- The diagonal coupling of a distribution with itself: mass `a i` stays at `i`. -/
def diagPlan (a : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => if i = j then a i else 0

/-
The diagonal coupling is a transport plan from `a` to `a` (for `a ≥ 0`).
-/

/-
A transport plan of a nonnegative ground cost has nonnegative total cost.
-/

/-
The cost of the diagonal coupling under a diagonal-vanishing ground cost is `0`.
-/

/-- The **finite optimal-transport (Wasserstein) value** of ground cost `d` between
distributions `a` and `b`: the infimum of the transport cost over feasible plans. -/
noncomputable def wValue (d : Fin n → Fin n → ℝ) (a b : Fin n → ℝ) : ℝ :=
  sInf (transportCost d '' feasibleSet a b)

/-
The cost image is bounded below by `0` for a nonnegative ground cost.
-/

/-
**Nonnegativity of the Wasserstein value.**
-/

/-
**Self-distance is zero.** If the ground cost vanishes on the diagonal and is
nonnegative, the Wasserstein value of a distribution to itself is `0`.
-/

/-
**Symmetry of the Wasserstein value** for a symmetric ground cost.
-/

end Novelty.OptimalTransport


