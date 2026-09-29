-- Prove2me | Definitions.Def_Novelty_BrenierKantorovich
-- name    : Novelty_BrenierKantorovich
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:08:48.668741+00:00
-- url     : https://prove2.me/theorems/c2f96ac4-2621-4bd5-8568-eed8b6723f91
-- title:
--   Aether Catalog definitions — Novelty_BrenierKantorovich
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.BrenierKantorovich`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/BrenierKantorovich.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_Brenier
import Definitions.Def_Novelty_Kantorovich

/-!
# Bridging Brenier and Kantorovich: the monotone permutation plan is optimal

This file connects the two developments of this directory:

* `Novelty.OptimalTransport.Kantorovich` — the Kantorovich transport polytope and
  cost (`IsTransportPlan`, `transportCost`);
* `Novelty.OptimalTransport.Brenier` — the discrete Brenier theorem
  (`brenier_monotone_optimal`, `quadraticMatchingCost`).

A permutation `σ` induces the **permutation coupling** `permPlan σ`
(`π i j = 1` iff `j = σ i`), a genuine Kantorovich transport plan between the
uniform marginals `(1,…,1)`.  Its transport cost is the matching cost
`∑ i, c i (σ i)`.  Specializing to the quadratic ground cost
`c i j = (x i - y j)^2` and invoking Brenier, we obtain:

* `perm_quadratic_optimal` — among permutation couplings, the identity (monotone)
  coupling minimizes the quadratic Kantorovich transport cost, provided the point
  clouds are sorted the same way.

This is the Kantorovich-side restatement of Brenier's theorem (optimal transport
*map* = monotone map), realized inside the transportation polytope.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): Brenier's "monotone matching is optimal" must be
expressible directly as optimality of a *transport plan* (the permutation matrix)
in the Kantorovich polytope.  Experiment (Experimenter): define `permPlan`, show it
is a Kantorovich `IsTransportPlan` for uniform marginals, compute its
`transportCost` as `∑ i, c i (σ i)`, and reduce optimality to
`brenier_monotone_optimal`.  Analysis (Analyst): the column-marginal computation is
exactly where the permutation/bijectivity is used (each target receives mass `1`
from a unique source).  Critique (Critic): optimality is proven only against the
permutation couplings, not the full polytope; closing that gap is Birkhoff–von
Neumann, which is absent from Mathlib and recorded as a future direction.
-- !-- end Lab Notes -- !--
-/

namespace Novelty.OptimalTransport

open scoped BigOperators

variable {n : ℕ}

/-- The permutation coupling: all mass at source `i` is sent to target `σ i`. -/
def permPlan (σ : Equiv.Perm (Fin n)) : Fin n → Fin n → ℝ :=
  fun i j => if j = σ i then 1 else 0




end Novelty.OptimalTransport


