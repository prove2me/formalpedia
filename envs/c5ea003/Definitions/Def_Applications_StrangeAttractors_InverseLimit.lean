-- Prove2me | Definitions.Def_Applications_StrangeAttractors_InverseLimit
-- name    : Applications_StrangeAttractors_InverseLimit
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:57:06.882404+00:00
-- url     : https://prove2.me/theorems/e02ff332-bf0c-4fbd-8bbf-30294b37b7f6
-- title:
--   Aether Catalog definitions — Applications_StrangeAttractors_InverseLimit
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.StrangeAttractors.InverseLimit`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/StrangeAttractors/InverseLimit.lean by skeleton subtraction
import Mathlib
/-
# Strange Attractors as Algebraic Objects — I. Inverse Limits of Finite Systems

This file builds the categorical/algebraic skeleton needed to treat a chaotic
attractor as an *inverse limit* of a diagram of finite combinatorial objects
(the boldest conjecture of the mission: the Lorenz attractor's topology is the
inverse limit of a diagram in the category of finite directed graphs).

We work with countable inverse systems indexed by `ℕ`:

      obj 0  ⟵  obj 1  ⟵  obj 2  ⟵  ⋯          (bonding maps `bond n`)

and their inverse limit, the set of *compatible threads*.

## Main results

* `InvSystem`                       — a countable inverse system of types/graphs.
* `InvLimit`                        — the inverse limit (compatible threads).
* `InvLimit.proj_bond`             — projections commute with bonding maps.
* `InvLimit.ext`                   — a thread is determined by its projections.
* `InvLimit.nonempty_of_surjective` — **the limit of a nonempty system with
    surjective bonding maps is nonempty** (the combinatorial heart: a Cantor-set
    transversal of an attractor never collapses).  This is the discrete
    Mittag-Leffler / dependent-choice phenomenon.

This is the **cross-domain bridge** target of the cycle: it links dynamical
systems (attractors) to category theory (inverse limits) and algebra.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): An attractor presented as a nested intersection of
neighbourhoods is the inverse limit of the finite nerves of those
neighbourhoods; the limit is never empty as long as each finite stage is
nonempty and the refinement maps are onto.
Experiment (Experimenter): Formalised inverse systems over `ℕ`, the limit as a
subtype of compatible threads, and proved nonemptiness from surjectivity by
building a thread with `Nat.rec` and a global choice section of the bonding maps.
Analysis (Analyst): Surjectivity is exactly the hypothesis that lets a chosen
base point be lifted indefinitely; without it the limit can be empty (e.g.
`ℤ ←(+1)— ℤ` style systems with shrinking images).  "True and not hard once the
choice section is isolated"; the subtlety is purely the dependent recursion.
Critique (Critic): The theorem is not vacuous — it produces a genuine element;
the surjectivity hypothesis is load-bearing (see the analysis).  No
`native_decide`, no definitional triviality.
Synthesis (PI): This is the reusable engine; the dyadic solenoid and the Lorenz
transversal instantiate it downstream.
-- !-- Lab Notes -- !--
-/

namespace StrangeAttractors

/-- A countable **inverse system**: a sequence of objects with bonding maps
`obj (n+1) → obj n`.  The objects are intended to be (vertex sets of) finite
directed graphs, the bonding maps graph morphisms. -/
structure InvSystem where
  /-- The object at stage `n`. -/
  obj : ℕ → Type
  /-- The bonding map from stage `n+1` down to stage `n`. -/
  bond : ∀ n, obj (n + 1) → obj n

/-- The **inverse limit** of an inverse system: compatible threads. -/
def InvLimit (S : InvSystem) : Type :=
  { x : ∀ n, S.obj n // ∀ n, S.bond n (x (n + 1)) = x n }

namespace InvLimit

/-- Projection of a thread to stage `n`. -/
def proj (S : InvSystem) (n : ℕ) (x : InvLimit S) : S.obj n := x.1 n


/-
A thread is determined by its projections.
-/

/-
**The inverse limit of a nonempty system with surjective bonding maps is
nonempty.**  This is the discrete Mittag-Leffler property / dependent choice:
a base point can be lifted along the surjections to a full compatible thread.
-/


end InvLimit

end StrangeAttractors


