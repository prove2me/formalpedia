-- Prove2me | Definitions.Def_Geometry_EmergentFixedPointKleene
-- name    : Geometry_EmergentFixedPointKleene
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:12:50.336897+00:00
-- url     : https://prove2.me/theorems/63f758d8-ee94-4d0f-8382-62dc54137b6b
-- title:
--   Aether Catalog definitions — Geometry_EmergentFixedPointKleene
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.EmergentFixedPointKleene`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/EmergentFixedPointKleene.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The Emergent Fixed Point as a Limit of Finite Self-Observation Stages

A recurring picture in the study of self-reference is that a system's stable
self-image should *emerge* as the limit of finitely many rounds of
self-observation: start from a completely uninformed state, apply the
observation operator once, twice, and so on, and pass to the limit.  The
present development turns this picture into a precise approximation theorem.

Working in a complete lattice of "observation states", we model a round of
self-observation by a monotone operator `f`.  The finite **stages** are the
iterates `f^[n] ⊥`, starting from the least (uninformed) state `⊥`, and the
**emergent state** is their supremum.  The main results are:

* `emergent_le_of_prefixed` — the emergent state lies below every pre-fixed
  point; in particular below every fixed point.  This needs only monotonicity.
* `emergent_le_lfp` — consequently the emergent state never exceeds the least
  fixed point guaranteed by the Knaster–Tarski theorem.
* `emergent_fixed` — if the observation operator is (countably) continuous,
  i.e. it commutes with suprema of increasing sequences, the emergent state is
  itself a fixed point.
* `emergent_eq_lfp` — the **Kleene approximation theorem**: for a continuous
  operator the emergent state *equals* the least fixed point.  The stable
  self-image is exactly the supremum of the finite self-observation stages.

The final section records the sharpness of the continuity hypothesis: on a
lattice with two limit levels there is a monotone but discontinuous operator
whose emergent state is strictly below its least fixed point.  Thus continuity
is not a technical convenience but the exact condition under which the limit of
finite stages captures the whole fixed point.

## References

- S. C. Kleene, *Introduction to Metamathematics* (1952), first-recursion
  theorem.
- B. Knaster and A. Tarski, lattice-theoretic fixed point theorem (1928, 1955).

-- !-- Lab Notes -- !--
-- Hypothesis (Hypothesizer): Ranked conjectures for a "synthetic domain
--   theory" account of the emergent fixed point:
--   (1) [bold] the least fixed point of a self-observation operator is the
--       supremum of the finite iterates of the least element — a genuine
--       approximation theorem, not merely an existence statement;
--   (2) the emergent supremum is always below the Knaster–Tarski least fixed
--       point, for any monotone operator;
--   (3) [bold] continuity of the operator is exactly the boundary: without it
--       the emergent supremum can be strictly smaller than the least fixed
--       point;
--   (4) concrete reachability operators realise the emergent point as a
--       maximal (top) state.
-- Experiment (Experimenter): (1) and (2) proved in full generality in a
--   complete lattice. (4) verified on the successor/reachability operator on
--   subsets of the naturals, whose emergent state is the whole set. (3)
--   witnessed by a discontinuous operator on two stacked limit levels.
-- Analysis (Analyst): Monotonicity alone controls the emergent point from
--   above (it is a pre-fixed-point bound); continuity is what closes the gap
--   from below by making the supremum a fixed point. The proof of the fixed
--   point property is a one-line index shift once continuity is available,
--   isolating precisely where the hypothesis is spent. The failure mode in the
--   discontinuous case is exactly that the operator "jumps" at the limit stage.
-- Critique (Critic): The main theorem is not `native_decide` or definitional;
--   it consumes an honest continuity hypothesis and reproduces the classical
--   Kleene fixed-point theorem. The boundary section prevents the theorem from
--   being read as unconditional: the discontinuous witness exhibits a strict
--   gap `emergent < lfp` and explicitly violates the continuity hypothesis.
-- Synthesis (PI): Together these give the "least emergent fixed point is the
--   supremum of finite stages from bottom" statement requested by the research
--   direction, with a sharp characterisation of when it holds.
-/

namespace EmergentFixedPoint

/-! ## Finite stages and the emergent state -/

variable {α : Type*} [CompleteLattice α] (f : α →o α)

/-- The `n`-th finite approximation stage: `n` rounds of self-observation
applied to the least (uninformed) state `⊥`. -/
def stage (n : ℕ) : α := (⇑f)^[n] ⊥

/-- The emergent state: the supremum of all finite self-observation stages. -/
def emergent : α := ⨆ n, stage f n






/-! ## The emergent state as a bound and as a fixed point -/





/-! ## Examples

Concrete instantiations of the emergent construction. -/

section Examples

/-- The **reachability operator** on subsets of `ℕ`: one round of observation
adds `0` and the successor of everything already present. -/
def reach : Set ℕ →o Set ℕ where
  toFun S := insert 0 (Nat.succ '' S)
  monotone' := fun _ _ h => Set.insert_subset_insert (Set.image_mono h)


end Examples

/-! ## Boundary: continuity is necessary

We exhibit a monotone but discontinuous operator whose emergent state is
*strictly* below its least fixed point.  The carrier is the lattice
`Ldbl := WithTop (WithTop ℕ)`, which stacks two limit levels above the natural
numbers:

```
  0 < 1 < 2 < ⋯ < ω < ω+1
```

where `ω = some ⊤` (the coerced top of the inner `WithTop ℕ`) and `ω+1 = ⊤`.
The operator `gapMap` sends each finite level to its successor and jumps the
first limit level `ω` straight to `ω+1`.  Its finite stages from `⊥` climb the
naturals, so the emergent state is `ω`; but the only fixed point is `ω+1`. -/

section Boundary

/-- Two limit levels above `ℕ`. -/
abbrev Ldbl := WithTop (WithTop ℕ)

/-- Successor on finite levels; the first limit level `ω = some ⊤` jumps to the
top `ω+1 = ⊤ = none`. -/
def gapMap : Ldbl → Ldbl
  | none => none
  | some none => none
  | some (some n) => some (some (n + 1))

lemma gapMap_mono : Monotone gapMap := by
  intro a b h
  match a, b with
  | none, none => exact le_refl _
  | none, some x => exact absurd (top_le_iff.mp h) (by simp)
  | some none, none => exact le_top
  | some none, some none => exact le_refl _
  | some none, some (some n) =>
      exfalso
      have h2 : (⊤ : WithTop ℕ) ≤ (n : WithTop ℕ) := WithTop.coe_le_coe.mp h
      exact absurd (top_le_iff.mp h2) (by simp)
  | some (some m), none => exact le_top
  | some (some m), some none => exact le_top
  | some (some m), some (some n) =>
      show gapMap (some (some m)) ≤ gapMap (some (some n))
      simp only [gapMap]
      exact WithTop.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by
        have : m ≤ n := WithTop.coe_le_coe.mp (WithTop.coe_le_coe.mp h); omega))

/-- The discontinuous operator as a bundled monotone map. -/
def gapHom : Ldbl →o Ldbl := ⟨gapMap, gapMap_mono⟩







end Boundary

end EmergentFixedPoint


