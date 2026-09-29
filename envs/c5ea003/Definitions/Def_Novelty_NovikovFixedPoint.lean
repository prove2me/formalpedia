-- Prove2me | Definitions.Def_Novelty_NovikovFixedPoint
-- name    : Novelty_NovikovFixedPoint
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:33:56.21578+00:00
-- url     : https://prove2.me/theorems/a81f8085-7ade-40fe-8d0a-d28ef8b6f4c8
-- title:
--   Aether Catalog definitions — Novelty_NovikovFixedPoint
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.NovikovFixedPoint`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/NovikovFixedPoint.lean by skeleton subtraction
import Mathlib

open Filter Topology

/-!
# Novikov-Fixed-Point: Unique Self-Consistent Histories for Causally Loop-Closed Spacetimes

The **Novikov Self-Consistency Principle** asserts that, in a spacetime containing
closed timelike curves (a "causally loop-closed" spacetime, e.g. one with a
traversable wormhole time machine), the *only* physically realisable histories are
those that are globally self-consistent: whatever influence a system exerts on its
own past must be exactly the influence that produced its present. A billiard ball
that travels back in time and strikes its earlier self may only follow a trajectory
that is consistent with having been struck.

Mathematically this is a **fixed-point condition**. Model the relevant boundary /
initial data on the causal loop by a point of a state space `α`, and let
`evolve : α → α` be the map that carries a candidate history once around the loop
(propagate forward, pass through the time machine, and read off the resulting
influence on the initial data). A history is *self-consistent* precisely when it is
a fixed point, `evolve x = x`.

We formalise the principle in the regime where the round-trip map is a
**contraction** (`rate < 1`): the loop damps discrepancies rather than amplifying
them. On a nonempty complete state space this is exactly the hypothesis of the
Banach fixed-point theorem, so a self-consistent history

* **exists**,
* is **unique**, and
* is the **limit of the naive relaxation iteration** `evolveⁿ x₀` from *any*
  starting guess `x₀` — the physical picture of "the timeline settling down".

## Main results

* `NovikovFixedPoint.CausalLoop.existsUnique` — existence and uniqueness of a
  self-consistent history (the Novikov principle as a theorem).
* `NovikovFixedPoint.CausalLoop.iterate_tendsto` — relaxation to self-consistency
  from an arbitrary initial guess.
* `NovikovFixedPoint.CausalLoop.dist_history_le` — an a-priori bound on how far any
  candidate lies from the self-consistent history (the *consistency defect*).
* `NovikovFixedPoint.stability` — a perturbation bound: the self-consistent history
  depends Lipschitz-continuously on the physics of the loop, so a small change of
  the round-trip law moves the timeline only a little.
* `NovikovFixedPoint.affineLoop` and `NovikovFixedPoint.affineLoop_history` — the
  textbook billiard-through-a-wormhole model `evolve x = a·x + b` with `|a| < 1`:
  its unique self-consistent value is exactly `b / (1 - a)`.
-/

namespace NovikovFixedPoint

variable {α : Type*} [MetricSpace α]

/-- A **causal loop** on a state space `α`: the round-trip self-consistency map
`evolve`, together with a contraction `rate < 1` witnessing that the loop damps
discrepancies. -/
structure CausalLoop (α : Type*) [MetricSpace α] where
  /-- The map carrying a candidate history once around the causal loop. -/
  evolve : α → α
  /-- The contraction rate of the round trip. -/
  rate : NNReal
  /-- The round-trip map is a contraction: it strictly shrinks distances. -/
  isContracting : ContractingWith rate evolve

variable [Nonempty α] [CompleteSpace α]

/-- The unique self-consistent history of the loop — the Novikov solution. -/
noncomputable def CausalLoop.history (L : CausalLoop α) : α :=
  ContractingWith.fixedPoint L.evolve L.isContracting








/-!
## The billiard-through-a-wormhole model

The canonical thought experiment behind the Novikov principle is a billiard ball
that enters a wormhole time machine, emerges in its own past, and deflects its
earlier self. Linearising the deflection law about a nominal trajectory gives an
affine round-trip map `evolve x = a·x + b` on the real line, where `x` records the
relevant one-dimensional datum (an impact parameter, say). The loop is damping
exactly when `|a| < 1`, and the Novikov principle then predicts a single consistent
value. We verify that this value is `b / (1 - a)`.
-/

/-- The affine billiard-through-a-wormhole causal loop `x ↦ a·x + b` on `ℝ`, damping
whenever `|a| < 1`. -/
noncomputable def affineLoop (a b : ℝ) (ha : |a| < 1) : CausalLoop ℝ where
  evolve := fun x => a * x + b
  rate := Real.toNNReal |a|
  isContracting := by
    constructor
    · rw [show (1 : NNReal) = Real.toNNReal 1 by simp,
        Real.toNNReal_lt_toNNReal_iff (by norm_num)]
      exact ha
    · rw [lipschitzWith_iff_dist_le_mul]
      intro x y
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (abs_nonneg a),
        show (a * x + b) - (a * y + b) = a * (x - y) by ring, abs_mul]


end NovikovFixedPoint


