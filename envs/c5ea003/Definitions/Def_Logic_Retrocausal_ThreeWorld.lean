-- Prove2me | Definitions.Def_Logic_Retrocausal_ThreeWorld
-- name    : Logic_Retrocausal_ThreeWorld
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:07:26.031752+00:00
-- url     : https://prove2.me/theorems/d3edd9b5-9900-4520-aa11-2d07bae86a0f
-- title:
--   Aether Catalog definitions — Logic_Retrocausal_ThreeWorld
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.Retrocausal.ThreeWorld`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/Retrocausal/ThreeWorld.lean by skeleton subtraction
import Mathlib
import Mathlib.Data.Fin.Basic

/-!
# A finite retrocausal Heyting semantics

This file gives a precise, deliberately modest mathematical model for the requested
ideas.  Truth is evaluated in the three-world chain `past ≤ present ≤ future`.
Heyting implication is the relative pseudocomplement.  `reverse` exchanges past and
future and fixes the present; it is an abstract time-reversal/CPT-like operation, not
a formalization of the physical CPT theorem.

The central distinction is machine checked: ordinary excluded middle fails at the
intermediate world, while `a ∨ reverse a = future` always holds.  The final results
show that backwards implication is governed by the same Heyting residuation law,
so the retrocausal connective does not force Boolean logic.
-/

namespace Retrocausal

/-- Truth values of a three-stage temporal Kripke chain. -/
inductive World
  | past | present | future
  deriving DecidableEq, Repr

open World

/-- The temporal/Kripke order. -/
def le : World → World → Prop
  | past, _ => True
  | present, present | present, future | future, future => True
  | _, _ => False

instance : LE World := ⟨le⟩
instance : DecidableRel le
  | past, _ => isTrue trivial
  | present, past => isFalse id
  | present, present => isTrue trivial
  | present, future => isTrue trivial
  | future, future => isTrue trivial
  | future, past => isFalse id
  | future, present => isFalse id

/-- Conjunction in the three-element chain. -/
def meet : World → World → World
  | past, _ | _, past => past
  | present, _ | _, present => present
  | future, future => future

/-- Disjunction in the three-element chain. -/
def join : World → World → World
  | future, _ | _, future => future
  | present, _ | _, present => present
  | past, past => past

/-- Heyting implication on a finite chain: `a ⇒ b = ⊤` if `a ≤ b`, and `b` otherwise. -/
def himp : World → World → World
  | past, _ => future
  | present, past => past
  | present, present | present, future => future
  | future, b => b

/-- Intuitionistic negation. -/
def hneg (a : World) : World := himp a past

/-- Abstract temporal reversal: effects at one endpoint are read as causes at the other. -/
def reverse : World → World
  | past => future
  | present => present
  | future => past

/-- A temporal alternative: at the undecided present, the future remains available. -/
def temporalNeg : World → World
  | past | present => future
  | future => past










/-- Backwards (retrocausal) implication is ordinary Heyting implication after reversing
both temporal arguments. -/
def retroImp (effect cause : World) : World :=
  himp (reverse effect) (reverse cause)




end Retrocausal


