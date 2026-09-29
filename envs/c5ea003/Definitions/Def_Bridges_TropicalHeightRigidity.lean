-- Prove2me | Definitions.Def_Bridges_TropicalHeightRigidity
-- name    : Bridges_TropicalHeightRigidity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:25.228478+00:00
-- url     : https://prove2.me/theorems/f31d4b8f-9a49-4160-ad7f-5696df9aafcc
-- title:
--   Aether Catalog definitions — Bridges_TropicalHeightRigidity
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalHeightRigidity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalHeightRigidity.lean by skeleton subtraction
import Mathlib

/-!
# Tropical Height Rigidity for Berggren Tree Valuations

This module formalizes a valuation-theoretic rigidity principle for the Berggren tree
of primitive Pythagorean triples. The main result is that finite-depth tropical
observables on Berggren orbits admit a decidable rigidity/collision stratification:
either a given observable value determines a unique word/triple, or there exists a
canonical collision certificate.

## Main definitions

* `BerggrenTropical.Gen` — the three Berggren generators {A, B, C}
* `BerggrenTropical.Word` — words in the free monoid on generators
* `BerggrenTropical.ObsVec` — observable vector: archimedean height + p-adic data
* `BerggrenTropical.theta` — the observable map from words to `ObsVec`
* `BerggrenTropical.WordsUpTo` — the finite set of all words of length ≤ d
* `BerggrenTropical.fiber` — preimage fiber of `theta` over `WordsUpTo d`

## Main results

* `fiber_singleton_or_collision` — every nonempty fiber is a singleton or has a collision
* `berggren_theta_decidable_rigidity` — decidable rigidity/collision dichotomy
* `generic_singleton_outside_exceptional` — augmented observables separate generic fibers
-/

open Matrix Finset

namespace BerggrenTropical

/-! ## §1. Berggren Generators and Word Algebra -/

/-- The three Berggren generators for the tree of primitive Pythagorean triples. -/
inductive Gen where
  | A | B | C
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Gen where
  elems := {Gen.A, Gen.B, Gen.C}
  complete := by intro x; cases x <;> simp

/-- A word is a list of generators, representing a path in the Berggren tree. -/
abbrev Word := List Gen

/-- Berggren matrix A: generates one branch of the Pythagorean tree. -/
def genMatA : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, -2, 2; 2, -1, 2; 2, -2, 3]

/-- Berggren matrix B: generates another branch. -/
def genMatB : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 2, 2; 2, 1, 2; 2, 2, 3]

/-- Berggren matrix C: generates the third branch. -/
def genMatC : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-1, 2, 2; -2, 1, 2; -2, 2, 3]

/-- Map each generator to its 3×3 integer matrix. -/
def genMatrix : Gen → Matrix (Fin 3) (Fin 3) ℤ
  | Gen.A => genMatA
  | Gen.B => genMatB
  | Gen.C => genMatC

/-- Evaluate a word to the product of its generator matrices.
    The empty word maps to the identity matrix. -/
def evalWord : Word → Matrix (Fin 3) (Fin 3) ℤ
  | [] => 1
  | g :: w => genMatrix g * evalWord w

/-- The root Pythagorean triple (3, 4, 5). -/
def rootTriple : Fin 3 → ℤ := ![3, 4, 5]

/-- The Pythagorean triple obtained by applying a word to the root. -/
def tripleOfWord (w : Word) : Fin 3 → ℤ :=
  evalWord w *ᵥ rootTriple

/-! ## §2. Observable Functions -/

/-- Archimedean height: maximum absolute value of coordinates. -/
def archHeight (t : Fin 3 → ℤ) : ℕ :=
  max (Int.natAbs (t 0)) (max (Int.natAbs (t 1)) (Int.natAbs (t 2)))

/-- p-adic valuation of the absolute value of a coordinate. -/
def vNatCoord (p : ℕ) (t : Fin 3 → ℤ) (i : Fin 3) : ℕ :=
  padicValNat p (Int.natAbs (t i))

/-- Observable vector: archimedean height together with 2-adic and 3-adic valuations
    of all three coordinates. This provides a "tropical snapshot" of the triple. -/
structure ObsVec where
  arch : ℕ
  v2x : ℕ
  v2y : ℕ
  v2z : ℕ
  v3x : ℕ
  v3y : ℕ
  v3z : ℕ
  deriving DecidableEq, Repr

instance : Inhabited ObsVec := ⟨⟨0, 0, 0, 0, 0, 0, 0⟩⟩

/-- Compute the observable vector of a triple. -/
def obsVecOf (t : Fin 3 → ℤ) : ObsVec where
  arch := archHeight t
  v2x := vNatCoord 2 t 0
  v2y := vNatCoord 2 t 1
  v2z := vNatCoord 2 t 2
  v3x := vNatCoord 3 t 0
  v3y := vNatCoord 3 t 1
  v3z := vNatCoord 3 t 2

/-- The observable map: compose tripleOfWord with obsVecOf. -/
def theta (w : Word) : ObsVec :=
  obsVecOf (tripleOfWord w)

/-! ## §3. Finite Word Sets and Fibers -/

/-- All words of exactly length n over the three generators. -/
def WordsOfLen : ℕ → Finset Word
  | 0 => {[]}
  | n + 1 => (Fintype.elems : Finset Gen).biUnion fun g =>
      (WordsOfLen n).map ⟨(g :: ·), List.cons_injective (a := g)⟩

/-- All words of length at most d. -/
def WordsUpTo (d : ℕ) : Finset Word :=
  (Finset.range (d + 1)).biUnion fun n => WordsOfLen n

/-
Membership in WordsOfLen is equivalent to having the right length.
-/


/-- The fiber of an observable value: all words of depth ≤ d mapping to that value. -/
def fiber (d : ℕ) (o : ObsVec) : Finset Word :=
  (WordsUpTo d).filter (fun w => theta w = o)


/-! ## §4. Core Finite-Depth Rigidity Theorem -/


/-
**Berggren theta decidable rigidity.**
    Every observable value in the image of θ at depth d admits a decidable
    classification: either a unique preimage or an explicit collision.
-/

/-
A singleton fiber yields a unique witness.
-/

/-
A fiber with card ≥ 2 yields two distinct elements with the same observable.
-/

/-
Positive fiber card iff the observable is in the image.
-/

/-! ## §5. Canonical Representatives and Certified Inversion -/


/-
Correctness of inversion: a trichotomy always holds.
-/

/-! ## §6. Augmented Observables with Modular Data -/

/-- Augmented observable vector: base observable plus mod-5 and mod-7 residues.
    The modular data provides additional separation power for fibers. -/
structure AugObsVec where
  base : ObsVec
  mod5x : ZMod 5
  mod5y : ZMod 5
  mod5z : ZMod 5
  mod7x : ZMod 7
  mod7y : ZMod 7
  mod7z : ZMod 7
  deriving DecidableEq, Repr

instance : Inhabited AugObsVec := ⟨⟨default, 0, 0, 0, 0, 0, 0⟩⟩

/-- Compute the augmented observable vector. -/
def augObsVecOf (t : Fin 3 → ℤ) : AugObsVec where
  base := obsVecOf t
  mod5x := (t 0 : ZMod 5)
  mod5y := (t 1 : ZMod 5)
  mod5z := (t 2 : ZMod 5)
  mod7x := (t 0 : ZMod 7)
  mod7y := (t 1 : ZMod 7)
  mod7z := (t 2 : ZMod 7)

/-- The augmented observable map. -/
def thetaAug (w : Word) : AugObsVec :=
  augObsVecOf (tripleOfWord w)


/-- The exceptional set: augmented observable values with non-singleton fibers. -/
def exceptionalSet (d : ℕ) : Finset AugObsVec :=
  ((WordsUpTo d).image thetaAug).filter (fun o =>
    1 < ((WordsUpTo d).filter (fun w => thetaAug w = o)).card)

/-
**Generic Separation Theorem (Main Theorem C).**
    Outside the exceptional set, every augmented observable fiber is a singleton.
-/

/-! ## §7. Tropical Valuation Properties -/







/-! ## §8. Concrete Computational Verification -/






end BerggrenTropical


