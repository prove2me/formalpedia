-- Prove2me | Definitions.Def_Algebra_A4ForkPinning_Character
-- name    : Algebra_A4ForkPinning_Character
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T15:39:35.500929+00:00
-- url     : https://prove2.me/theorems/4e507570-3efd-45f8-97ae-625e347620e0
-- title:
--   Aether Catalog definitions — Algebra_A4ForkPinning_Character
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.A4ForkPinning.Character`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/A4ForkPinning/Character.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_A4ForkPinning_GroupA4
import Definitions.Def_Algebra_A4ForkPinning_Resolvent
/-
# Both sides of the cubic pinning are the same group `C₃`

The pinning statement "`Frob p ∈ V₄` ⟺ `p` is a cube mod `9`" is an identification
of two characters of order three:

* on the Galois side, the character of `A₄^ab = A₄/V₄`;
* on the arithmetic side, the cubic residue character of `(ℤ/9)ˣ` modulo cubes.

This file bundles both as honest group homomorphisms and shows that the two
groups involved are isomorphic — the shape of the Artin reciprocity square that
class field theory provides for the conductor-`9` cyclic cubic field.

* `A4ForkPinning.chiA4Hom` — the cubic character `A₄ →* C₃`, with
  `chiA4Hom_ker` (`ker = V₄`) and `chiA4Hom_surjective`;
* `A4ForkPinning.chi9Hom` — the cubic residue character `(ℤ/9)ˣ →* C₃`, with
  `chi9Hom_ker_eq_cubes` and `chi9Hom_surjective`;
* `A4ForkPinning.card_units_quotient_cubes` — `|(ℤ/9)ˣ / cubes| = 3`;
* `A4ForkPinning.artin_shape` — `A₄^ab ≃* (ℤ/9)ˣ / cubes`: the Galois side and the
  ray-class side of the pinning are the *same* cyclic group of order three.
-/

namespace A4ForkPinning

open Equiv Equiv.Perm Finset

/-! ## The Galois-side character -/

/-- The cubic character of `A₄`, bundled as a homomorphism to `C₃`. -/
def chiA4Hom : alternatingGroup (Fin 4) →* Multiplicative (ZMod 3) where
  toFun g := Multiplicative.ofAdd (chi (g : Equiv.Perm (Fin 4)))
  map_one' := by decide
  map_mul' g h := by
    have := chi_mul (g : Equiv.Perm (Fin 4)) (h : Equiv.Perm (Fin 4))
      (mem_alternatingGroup.1 g.2) (mem_alternatingGroup.1 h.2)
    simpa [Multiplicative.ofAdd] using congrArg Multiplicative.ofAdd this



/-! ## The arithmetic-side character -/

/-- The cubic residue character mod `9`, bundled as a homomorphism `(ℤ/9)ˣ →* C₃`. -/
def chi9Hom : (ZMod 9)ˣ →* Multiplicative (ZMod 3) where
  toFun u := Multiplicative.ofAdd (chi9 (u : ZMod 9))
  map_one' := by decide
  map_mul' u v := by
    have := chi9_mul (u : ZMod 9) (v : ZMod 9) u.isUnit v.isUnit
    simpa [Multiplicative.ofAdd] using congrArg Multiplicative.ofAdd this

/-- The subgroup of cubes in `(ℤ/9)ˣ`. -/
def cubes9 : Subgroup (ZMod 9)ˣ := MonoidHom.range (powMonoidHom 3)

theorem mem_cubes9 {x : (ZMod 9)ˣ} : x ∈ cubes9 ↔ ∃ y : (ZMod 9)ˣ, y ^ 3 = x := Iff.rfl

instance : DecidablePred (fun x : (ZMod 9)ˣ => x ∈ cubes9) :=
  fun _ => decidable_of_iff _ mem_cubes9.symm



theorem card_cubes9 : Nat.card cubes9 = 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

/-- `|(ℤ/9)ˣ / cubes| = 3`: the cubic residue symbol mod `9` has exactly three values. -/
theorem card_units_quotient_cubes : Nat.card ((ZMod 9)ˣ ⧸ cubes9) = 3 := by
  have hcard : Nat.card ((ZMod 9)ˣ) = 6 := by
    rw [Nat.card_eq_fintype_card]; decide
  have h := Subgroup.card_mul_index cubes9
  rw [card_cubes9, hcard] at h
  have : cubes9.index = 3 := by omega
  simpa [Subgroup.index] using this

/-! ## Both sides agree -/

instance : IsCyclic (Abelianization (alternatingGroup (Fin 4))) :=
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  isCyclic_of_prime_card card_abelianization_alternating

instance : IsCyclic ((ZMod 9)ˣ ⧸ cubes9) :=
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  isCyclic_of_prime_card card_units_quotient_cubes


end A4ForkPinning


