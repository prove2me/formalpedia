-- Prove2me | Definitions.Def_Novelty_ReversibleElementary
-- name    : Novelty_ReversibleElementary
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:39:30.663121+00:00
-- url     : https://prove2.me/theorems/1c3e5a57-adc8-47e3-8333-ef77d42e1eee
-- title:
--   Aether Catalog definitions — Novelty_ReversibleElementary
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ReversibleElementary`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ReversibleElementary.lean by skeleton subtraction
import Mathlib

/-!
# Reversible elementary cellular automata

This file gives a finite, machine-checked correction to the proposed “local-rule
permutation” picture.  An elementary local rule has type `Bool³ → Bool`, so it
is not a permutation of the eight neighborhoods.  Reversibility concerns the
induced global map on configurations.

We prove a chain of structural results for the six projection/complement rules,
then exhaustively classify the rules which are bijective on cyclic configurations
of sizes 1 through 4.  The finite test leaves exactly Wolfram rules
15, 51, 85, 170, 204, and 240.  Since each of these six is proved reversible on
every nonempty finite cycle, the test also gives a certified obstruction of
period at most four for every other elementary rule.
-/

namespace ReversibleElementary

abbrev Config (n : ℕ) := Fin n → Bool
abbrev LocalRule := Bool → Bool → Bool → Bool

/-- The index `4l + 2c + r` of a Boolean neighborhood. -/
def neighborhoodIndex (l c r : Bool) : ℕ :=
  4 * l.toNat + 2 * c.toNat + r.toNat

/-- Elementary rule with Wolfram number `w`. -/
def wolframRule (w : Fin 256) : LocalRule := fun l c r =>
  Nat.testBit w.val (neighborhoodIndex l c r)

/-- Cyclic successor. -/
def rightIdx {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

/-- Cyclic predecessor. -/
def leftIdx {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + n - 1) % n, Nat.mod_lt _ hn⟩

/-- Global map induced on a nonempty finite cyclic configuration. -/
def globalMap (f : LocalRule) {n : ℕ} (hn : 0 < n) (x : Config n) : Config n :=
  fun i => f (x (leftIdx hn i)) (x i) (x (rightIdx hn i))

/-- Reversibility on the cycle of length `n` (false for the empty cycle). -/
def ReversibleOn (n : ℕ) (w : Fin 256) : Prop :=
  if hn : 0 < n then Function.Bijective (globalMap (wolframRule w) hn) else False

instance (n : ℕ) (w : Fin 256) : Decidable (ReversibleOn n w) := by
  unfold ReversibleOn
  split <;> infer_instance

/-- Reversibility on every nonempty finite cyclic configuration space. -/
def UniversallyReversible (w : Fin 256) : Prop :=
  ∀ n (hn : 0 < n), Function.Bijective (globalMap (wolframRule w) hn)














/-- A Boolean radius-one rule is coordinate-permutative when it reads exactly
one neighborhood coordinate through a permutation of the Boolean alphabet. -/
def IsSingleCoordinate (f : LocalRule) : Prop :=
  (∃ e : Equiv.Perm Bool, ∀ l c r, f l c r = e l) ∨
  (∃ e : Equiv.Perm Bool, ∀ l c r, f l c r = e c) ∨
  (∃ e : Equiv.Perm Bool, ∀ l c r, f l c r = e r)

instance (f : LocalRule) : Decidable (IsSingleCoordinate f) := by
  unfold IsSingleCoordinate
  infer_instance



/-! ## Alphabet-independent reversible dynamics

The elementary classification above is binary, but its positive mechanism does
not depend on the alphabet being Boolean. A local rule that reads one site and
then applies an alphabet permutation is reversible over every alphabet.
-/

/-- Configurations over an arbitrary alphabet. -/
abbrev ConfigOver (α : Type*) (n : ℕ) := Fin n → α

/-- Radius-one local rules over an arbitrary alphabet. -/
abbrev LocalRuleOver (α : Type*) := α → α → α → α

/-- The cyclic global map of an arbitrary-alphabet radius-one rule. -/
def globalMapOver {α : Type*} (f : LocalRuleOver α) {n : ℕ} (hn : 0 < n)
    (x : ConfigOver α n) : ConfigOver α n :=
  fun i => f (x (leftIdx hn i)) (x i) (x (rightIdx hn i))

/-- Applying an alphabet equivalence after permuting the sites is an equivalence
of configuration spaces. -/
def coordinateAlphabetEquiv {α : Type*} {n : ℕ}
    (p : Equiv.Perm (Fin n)) (e : Equiv.Perm α) :
    ConfigOver α n ≃ ConfigOver α n where
  toFun x i := e (x (p i))
  invFun x i := e.symm (x (p.symm i))
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp




end ReversibleElementary


