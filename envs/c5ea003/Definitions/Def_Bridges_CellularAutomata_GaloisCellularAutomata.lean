-- Prove2me | Definitions.Def_Bridges_CellularAutomata_GaloisCellularAutomata
-- name    : Bridges_CellularAutomata_GaloisCellularAutomata
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:17:04.850579+00:00
-- url     : https://prove2.me/theorems/2363973d-fcf8-4f76-b98d-4b9d0c69a4c0
-- title:
--   Aether Catalog definitions — Bridges_CellularAutomata_GaloisCellularAutomata
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.CellularAutomata.GaloisCellularAutomata`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/CellularAutomata/GaloisCellularAutomata.lean by skeleton subtraction
import Mathlib

/-!
# Galois Theory of Cellular Automata: Reversible Dynamics

We formalize the group structure of reversible elementary cellular automata
(ECAs) on periodic binary configurations. An elementary CA has radius 1 and
binary alphabet {0,1}, giving 256 possible local rules (Wolfram numbering).

## Main Results

* `globalMap_rule204_eq_id` — Rule 204 implements the identity map
* `globalMap_rule170_bijective` — Rule 170 (left shift) is bijective
* `globalMap_rule051_bijective` — Rule 51 (complement) is bijective
* `globalMap_rule000_not_injective` — Rule 0 is not injective for n ≥ 2
* `reversible_eca_periodic` — Every config under a reversible CA is periodic
* `shift_complement_comm` — Shift and complement commute as global maps

## Novel Definitions

* `CADynamicalSystem` — A CA viewed as a discrete dynamical system with orbit structure
* `ReversibilityIndex` — Measures how far a rule is from being reversible
-/

namespace GaloisCA

/-! ## Configuration Space and Local Rules -/

/-- Configuration: a periodic binary string of length n -/
abbrev Config (n : ℕ) := Fin n → Bool

/-- An elementary CA local rule maps a 3-cell neighborhood (left, center, right) to a cell value -/
abbrev LocalRule := Bool → Bool → Bool → Bool

/-! ## Cyclic Index Operations on Fin n -/

/-- Right neighbor index (i+1 mod n) -/
def rightIdx {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

/-- Left neighbor index (i-1 mod n, computed as i+n-1 mod n) -/
def leftIdx {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + n - 1) % n, Nat.mod_lt _ hn⟩

/-! ## Global Map -/

/-- The global map induced by a local rule on periodic configurations of size n.
    Each cell's new value is determined by applying the rule to the cell and its neighbors. -/
def globalMap (f : LocalRule) {n : ℕ} (hn : 0 < n)
    (s : Config n) : Config n := fun i =>
  f (s (leftIdx hn i)) (s i) (s (rightIdx hn i))

/-! ## Named Elementary CA Rules (Wolfram Numbering)

The 6 reversible elementary CAs are exactly the rules whose output depends
on a single input variable, composed with an optional negation:
- Center-dependent: Rule 204 (c), Rule 51 (¬c)
- Right-dependent: Rule 170 (r), Rule 85 (¬r)
- Left-dependent: Rule 240 (l), Rule 15 (¬l)
-/

/-- Rule 204: identity — output equals center cell -/
def rule204 : LocalRule := fun _ c _ => c

/-- Rule 170: left shift — output equals right neighbor -/
def rule170 : LocalRule := fun _ _ r => r

/-- Rule 240: right shift — output equals left neighbor -/
def rule240 : LocalRule := fun l _ _ => l

/-- Rule 51: complement — output is NOT of center cell -/
def rule051 : LocalRule := fun _ c _ => !c



/-- Rule 0: constant false — all cells become 0 -/
def rule000 : LocalRule := fun _ _ _ => false

/-! ## Novel Definition: CA Dynamical System -/





/-! ## Novel Definition: Reversibility Index -/

/-- The reversibility index measures the failure of injectivity.
    It counts how many configurations share their image with another
    distinct configuration. For reversible CAs, this is 0. -/
noncomputable def reversibilityIndex {n : ℕ} (f : Config n → Config n) : ℕ :=
  Finset.card (Finset.univ.filter (fun s =>
    ∃ t : Config n, t ≠ s ∧ f t = f s))

/-! ## Cyclic Index Lemmas -/

/-
Left and right index operations are inverse: leftIdx ∘ rightIdx = id
-/

/-
Right and left index operations are inverse: rightIdx ∘ leftIdx = id
-/







/-! ## Rule Characterizations -/





/-! ## Bijection Proofs for Reversible Rules -/

/-
Rule 170 (left shift) is bijective
-/

/-
Rule 240 (right shift) is bijective
-/

/-
Rule 51 (complement) is an involution
-/


/-
Rule 170 and Rule 240 are inverses
-/

/-
Rule 240 and Rule 170 are inverses
-/

/-! ## Non-Reversibility of Rule 0 -/


/-
Rule 0 is not injective for n ≥ 1 (since all configs map to the same thing)
-/

/-! ## Commutativity: Shift and Complement Commute -/

/-- The complement operation on configurations -/
def complementConfig {n : ℕ} (s : Config n) : Config n := fun i => !(s i)

/-- The left shift operation on configurations -/
def leftShift {n : ℕ} (hn : 0 < n) (s : Config n) : Config n :=
  s ∘ rightIdx hn

/-
Complement is an involution
-/

/-
Left shift and complement commute as operations on configurations
-/

/-! ## Periodicity under Reversible CAs -/

/-
Every configuration under a bijective map on a finite type is periodic.
    This is a fundamental consequence of the pigeonhole principle:
    the orbit {s, f(s), f²(s), ...} in a finite set must eventually repeat.
-/

/-! ## Reversibility Index Properties -/

/-
The reversibility index of a bijective map is 0
-/

/-
The reversibility index of a constant map on a space with ≥ 2 elements is positive
-/

/-! ## Structure Theorem: Reversible ECA Classification -/

/-- A local rule is "single-input" if the output depends on exactly one of l, c, r,
    possibly composed with negation. This characterizes the reversible elementary CAs. -/
def isSingleInput (f : LocalRule) : Prop :=
  (∃ g : Bool → Bool, Function.Bijective g ∧ ∀ l c r, f l c r = g l) ∨
  (∃ g : Bool → Bool, Function.Bijective g ∧ ∀ l c r, f l c r = g c) ∨
  (∃ g : Bool → Bool, Function.Bijective g ∧ ∀ l c r, f l c r = g r)

/-
Every single-input rule with a bijective function gives a bijective global map
-/

/-! ## Conjecture: Universal Reversibility Classification -/

/-- A rule is *universally reversible* if its global map is bijective
    for every configuration size n ≥ 1. -/
def isUniversallyReversible (f : LocalRule) : Prop :=
  ∀ n : ℕ, (hn : 0 < n) → Function.Bijective (globalMap f hn)



end GaloisCA


