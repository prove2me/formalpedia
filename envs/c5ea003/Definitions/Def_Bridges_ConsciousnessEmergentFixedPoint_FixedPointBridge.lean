-- Prove2me | Definitions.Def_Bridges_ConsciousnessEmergentFixedPoint_FixedPointBridge
-- name    : Bridges_ConsciousnessEmergentFixedPoint_FixedPointBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:19:20.79588+00:00
-- url     : https://prove2.me/theorems/8cbf3263-22a5-472e-882f-26e18458632b
-- title:
--   Aether Catalog definitions — Bridges_ConsciousnessEmergentFixedPoint_FixedPointBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ConsciousnessEmergentFixedPoint.FixedPointBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ConsciousnessEmergentFixedPoint/FixedPointBridge.lean by skeleton subtraction
import Mathlib

/-!
# Consciousness as an Emergent Fixed Point

A self-model is represented by an interpretation map `A → (A → B)`.  Pointwise
completeness says that every `B`-valued behaviour is represented by a state.
Lawvere's diagonal argument then produces a fixed point for every endomorphism
of `B`.  The representing state supplies a literal closed self-observation loop.

The final section records a type-theoretic form of Yoneda faithfulness:
precomposition by a map is completely determined by its action on the identity.
This connects the exponential object `A → B` used by the self-model to the
representable functor of `A`.
-/

open Function

namespace ConsciousnessEmergentFixedPoint

universe u v w

/-- An extensional self-model of states `A` with observations in `B`. -/
structure SelfModel (A : Type u) (B : Type v) where
  /-- The observer represented by each state. -/
  interpret : A → (A → B)

/-- Completeness means that every possible observer is represented by a state. -/
def SelfModel.Complete {A : Type u} {B : Type v} (M : SelfModel A B) : Prop :=
  Surjective M.interpret

/-- Diagonal evaluation is the observation made by a state of its own observer. -/
def SelfModel.diagonal {A : Type u} {B : Type v} (M : SelfModel A B) (a : A) : B :=
  M.interpret a a

/-- A state is a strange-loop witness for `g` when it represents the transformed
self-observation and its diagonal observation is stable under `g`. -/
def SelfModel.IsStrangeLoop {A : Type u} {B : Type v}
    (M : SelfModel A B) (g : B → B) (a : A) : Prop :=
  (M.interpret a = fun x => g (M.diagonal x)) ∧
    g (M.diagonal a) = M.diagonal a









/-- The transition graph of an endomorphism. -/
def OrbitStep {B : Type v} (g : B → B) (x y : B) : Prop := y = g x

/-- A finite closed walk in the orbit graph.  Its length is the number of
applications of the observation transformer. -/
def ClosedOrbit {B : Type v} (g : B → B) (b : B) (n : ℕ) : Prop :=
  g^[n] b = b




/-- Precomposition is the action of the contravariant representable functor
`Hom(-, X)` on a map `f : A → B`. -/
def yonedaPrecompose {A : Type u} {B : Type v} (f : A → B)
    (X : Type w) (h : B → X) : A → X :=
  h ∘ f





end ConsciousnessEmergentFixedPoint


