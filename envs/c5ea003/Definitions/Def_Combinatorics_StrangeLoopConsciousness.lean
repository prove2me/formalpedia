-- Prove2me | Definitions.Def_Combinatorics_StrangeLoopConsciousness
-- name    : Combinatorics_StrangeLoopConsciousness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:55:35.981566+00:00
-- url     : https://prove2.me/theorems/68428359-878e-432b-911c-f96749930195
-- title:
--   Aether Catalog definitions — Combinatorics_StrangeLoopConsciousness
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.StrangeLoopConsciousness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/StrangeLoopConsciousness.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# I Am a Strange Loop, Part III: A Conscious System Models Itself

We formalise Hofstadter's operative definition of a conscious system as one
that *"contains a representation of its own state that it can inspect."*  We
model a system by:

* a space of **states** `S`;
* a space of **observations** `B` the system can make about a whole state;
* an **inspection map** `inspect : S → (S → B)` — each state carries an
  internal model of how *every* state would be observed.

The loop is **complete** (`Conscious`) when `inspect` is point-surjective:
the system's internal models cover *all* observation-behaviours of itself —
there is nothing about its own observable structure that it cannot represent.

From this single definition we derive both faces of the strange loop:

* `conscious_forces_fixedPoints`: a complete self-model necessarily produces
  fixed points of every observation-transformation — the self-referential
  "I" is *forced* to exist (Lawvere, positive face).
* `no_conscious_bool_model`, `no_conscious_prop_model`: **no** system can have a
  *complete* boolean/propositional self-model — a Gödelian limit: total,
  perfect self-knowledge is impossible (Cantor, negative face).
* `selfNegation_never_inspected`: the state's honest self-assessment
  "I do not observe-true of my own model" is never itself an inspected
  behaviour — the halting/liar obstruction as the price of self-awareness.

This file is fully self-contained (Lawvere's lemma is reproved locally).
-/

namespace StrangeLoop.Consciousness

universe u v

/-! ## Systems with a self-model -/

/-- A **self-modelling system**: states `S`, observations `B`, and an
`inspect`ion map assigning to each state an internal model of the whole
observation-behaviour of the system. -/
structure SelfModel (S : Type u) (B : Type v) where
  /-- Each state carries an internal representation of how every state is
  observed. -/
  inspect : S → (S → B)

/-- A self-model is **conscious** when its inspection is point-surjective: every
observation-behaviour of the system is internally represented by some state.
This is the formal "strange loop closing on itself". -/
def SelfModel.Conscious {S : Type u} {B : Type v} (M : SelfModel S B) : Prop :=
  Function.Surjective M.inspect

/-! ## The positive face: consciousness forces the self-referential "I" -/


/-! ## The negative face: perfect self-knowledge is impossible -/



/-! ## The halting/liar obstruction as the price of self-awareness -/



/-! ## Summary: the two faces are one theorem

`conscious_forces_fixedPoints` (a self-model, if complete, *must* generate a
self-referential fixed point) and `no_conscious_bool_model` /
`no_conscious_prop_model` (a self-model *cannot* be complete over a
fixed-point-free observation space) are the positive and negative readings of
the same diagonal.  Selfhood is exactly the fixed point that a self-model is
forced to contain and simultaneously forbidden to fully survey. -/

end StrangeLoop.Consciousness


