-- Prove2me | Definitions.Def_Geometry_QuantumSurreal_StandardPartMeasure
-- name    : Geometry_QuantumSurreal_StandardPartMeasure
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:51:57.571127+00:00
-- url     : https://prove2.me/theorems/495407d5-1193-475e-87d8-7178462b3db8
-- title:
--   Aether Catalog definitions — Geometry_QuantumSurreal_StandardPartMeasure
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.QuantumSurreal.StandardPartMeasure`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/QuantumSurreal/StandardPartMeasure.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The standard part collapses an infinitesimal measure to a Dirac measure

This is the *classical shadow* companion to the quantum-surreal state model.  There, amplitudes
live in the hyperreals `ℝ*` and the measurement rule is the standard part
`Hyperreal.st : ℝ* → ℝ`; an infinitesimal branch becomes unobservable.  Here we prove the exact
order-theoretic analogue for a finitely additive infinitesimal probability model.

That model uses the value ring `LexRat = ℚ × ℚ`, where `(a, b)` denotes `a + b·ε` with `ε` a
positive infinitesimal.  The sample space `Option (Fin n)` has `n` "visible" atoms each of weight
`ε` and one "reservoir" atom `none` of weight `1 - n·ε`, giving total mass `1`.

The `LexRat` construction, its atom weights, event probability `prob`, `visiblePart`, the closed
form `prob_eq_closed_form` and finite additivity `prob_union_disjoint` describe the underlying
finite infinitesimal model.  The new content is the *standard-part functional* and the collapse
theorem.

## New results

* `stdPart` — the standard-part functional `LexRat → ℚ`, taking the real (order-dominant)
  component.
* `stdPart_prob_dirac` — **the collapse**: `stdPart (prob n A) = 1` if the reservoir atom is in
  `A`, and `0` otherwise.  Observationally, the infinitesimal weight `ε` carried by every visible
  atom vanishes and all probability concentrates on the reservoir — the standard part of the
  infinitesimal measure is the Dirac measure `δ_none`.
* `stdPart_prob_univ`, `stdPart_visible_zero` — the total observed mass is `1` while each visible
  atom is observed with probability `0`.
* `stdPart_additive` — the observed measure is finitely additive.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the standard-part map that turns quantum hyperreal amplitudes into
ordinary probabilities should, applied to the catalog's `LexRat` infinitesimal measure, erase
exactly the infinitesimal (visible-atom) mass and leave a genuine real probability measure.

Experiment (Experimenter): for `n = 3`, `prob univ = (1, 0)` and each `prob {some i} = (0, 1)`.
Taking first coordinates gives `1` and `0` — the reservoir keeps all observable mass.

Analysis (Analyst): the catalog measure was *finitely additive and normalized in `LexRat`* but had
no notion of "observation".  The missing ingredient was a standard-part functional; supplying it
turns the infinitesimal measure into the Dirac measure on the reservoir.  This is the discrete,
order-theoretic mirror of `observedProb_infinitesimal_eq_zero` in the hyperreal quantum file.

Critique (Critic): `stdPart_prob_dirac` is not definitional trivia — it rests on the catalog's
`prob_eq_closed_form`, an induction over the finite event.  The additivity theorem uses the
reproduced `prob_union_disjoint`.  No result is `True`/`native_decide`-only.

Synthesis (PI): "standard part" is a single unifying observation functional — `Hyperreal.st` in
the continuous quantum model, `Prod.fst` in the discrete lexicographic model — and in both settings
it annihilates infinitesimal probability while preserving normalization and additivity.
-- !-- Lab Notes -- !--
-/

/-- The value type of the infinitesimal probability model: a pair `(a, b)` read as `a + b·ε`.
The first coordinate is the appreciable part and the second is infinitesimal. -/
abbrev LexRat := ℚ × ℚ

namespace LexRat




end LexRat

namespace InfinitesimalProbability

open LexRat

/-- Atom weights: reservoir `none` carries `1 - n·ε`, each visible atom `some i` carries `ε`.
Reproduced from the catalog. -/
def atomWeight (n : ℕ) : Option (Fin n) → LexRat
  | none => ((1 : ℚ), -(n : ℚ))
  | some _ => ((0 : ℚ), (1 : ℚ))


/-- The probability of an event is the finite sum of its atom weights. -/
def prob (n : ℕ) (A : Finset (Option (Fin n))) : LexRat := A.sum (atomWeight n)

/-- The visible indices whose atom belongs to the event. -/
def visiblePart (n : ℕ) (A : Finset (Option (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter fun i => some i ∈ A




/-! ## New content: the standard-part collapse -/

/-- The **standard-part functional** on `LexRat`: the real, order-dominant component of `a + b·ε`.
This is the discrete analogue of `Hyperreal.st`. -/
def stdPart (x : LexRat) : ℚ := x.1





end InfinitesimalProbability


