-- Prove2me | Definitions.Def_Novelty_Kantorovich
-- name    : Novelty_Kantorovich
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:08:05.951041+00:00
-- url     : https://prove2.me/theorems/f647b179-bb76-49c7-b615-b13fce02bffe
-- title:
--   Aether Catalog definitions — Novelty_Kantorovich
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Kantorovich`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Kantorovich.lean by skeleton subtraction
import Mathlib

/-!
# Finite Kantorovich optimal transport

We formalize the Kantorovich optimal transport problem in the finite (discrete)
setting, where source masses live on `Fin n` and target masses on `Fin m`.

A *transport plan* (coupling) `π : Fin n → Fin m → ℝ` is a nonnegative matrix whose
row marginals equal the source masses `a` and whose column marginals equal the
target masses `b`.  The *transport cost* w.r.t. a cost matrix `c` is
`∑ i, ∑ j, π i j * c i j`.

The main results are:

* `productPlan_isTransportPlan` — the independent coupling `a ⊗ b` is feasible
  whenever `a`, `b` are probability vectors, so the feasible set is nonempty;
* `isCompact_feasibleSet` — the feasible polytope is compact (closed + bounded in
  a finite-dimensional space);
* `exists_optimal_plan` — **existence of an optimal transport plan**: the
  Kantorovich infimum is attained.  This is the discrete Kantorovich existence
  theorem.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): in the finite setting the Kantorovich problem is a
linear program over a transportation polytope; existence of a minimizer should
follow from compactness of the feasible set and continuity of the linear cost.
Experiment (Experimenter): define plans/cost/feasible set over `ℝ`, prove the
product coupling is feasible (nonemptiness), prove the feasible set is closed and
bounded hence compact, and conclude existence via `IsCompact.exists_isMinOn`.
Analysis (Analyst): the only delicate point is the bound — each entry is squeezed
between `0` and its row sum `a i`, and row sums are nonnegative because they are
sums of nonnegative entries, so the whole polytope sits in a fixed ball.
Critique (Critic): existence does not need `a`, `b` to be probability vectors, only
nonemptiness of the feasible set; we keep `exists_optimal_plan` maximally general
and provide nonemptiness separately for probability vectors.
-- !-- end Lab Notes -- !--
-/

namespace Novelty.OptimalTransport

open scoped BigOperators
open Set

variable {n m : ℕ}

/-- `π` is a transport plan (coupling) between source masses `a` and target masses
`b`: it is entrywise nonnegative, its row marginals equal `a`, and its column
marginals equal `b`. -/
def IsTransportPlan (a : Fin n → ℝ) (b : Fin m → ℝ) (π : Fin n → Fin m → ℝ) : Prop :=
  (∀ i j, 0 ≤ π i j) ∧ (∀ i, ∑ j, π i j = a i) ∧ (∀ j, ∑ i, π i j = b j)

/-- The total Kantorovich transport cost of a plan `π` w.r.t. cost matrix `c`. -/
def transportCost (c : Fin n → Fin m → ℝ) (π : Fin n → Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, π i j * c i j

/-- The feasible set (transportation polytope) of plans between `a` and `b`. -/
def feasibleSet (a : Fin n → ℝ) (b : Fin m → ℝ) : Set (Fin n → Fin m → ℝ) :=
  {π | IsTransportPlan a b π}

/-- The independent coupling `a ⊗ b`, `π i j = a i * b j`. -/
def productPlan (a : Fin n → ℝ) (b : Fin m → ℝ) : Fin n → Fin m → ℝ :=
  fun i j => a i * b j

/-
The independent coupling of two probability vectors is a transport plan.
-/



/-
The feasible set is closed.
-/

/-
The feasible set is bounded.
-/



end Novelty.OptimalTransport


