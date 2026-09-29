-- Prove2me | Definitions.Def_mme_stothers_phi233_cyclic_affine_hash
-- name    : mme_stothers_phi233_cyclic_affine_hash
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T23:22:22.788832+00:00
-- url     : https://prove2.me/theorems/eb4abfa1-3295-461a-b7b7-886da44adeaf
-- title:
--   Cyclic affine hash for the Phi233 completion family
-- statement:
--   For five-grade Phi233 addresses, the coordinate support relation is $x+y+z=4$. These definitions implement the associated doubled affine hashes $2x$, $2y$, and $4-z$, combine three cyclic copies with coefficients $(1,4,-2)$, and add a common random shift plus one affine offset. The resulting hash is designed to obey the arithmetic-progression identity on every supported cyclic mixture while retaining a free common-label coordinate for exact fiber counts.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 5, pp. 356-360 and 365-367; affine Salem--Spencer hashing for the fourth-power Phi233 constituent.

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_mme_stothers_phi233_cyclic_ambient_data

open BigOperators

namespace MME.StothersFourth.Phi233

set_option autoImplicit false

def doubledXHash
    {R : Type} [CommRing R] {N : ℕ}
    (b : R) (w : Fin (2 * N) → R)
    (x : Fin (2 * N) → Fin 5) : R :=
  2 * b + ∑ j, ((2 * (x j).val : ℕ) : R) * w j

def doubledYHash
    {R : Type} [CommRing R] {N : ℕ}
    (b : R) (w : Fin (2 * N) → R)
    (y : Fin (2 * N) → Fin 5) : R :=
  2 * b + ∑ j, ((2 * (y j).val : ℕ) : R) * w j

def doubledZHash
    {R : Type} [CommRing R] {N : ℕ}
    (b : R) (w : Fin (2 * N) → R)
    (z : Fin (2 * N) → Fin 5) : R :=
  2 * b + ∑ j, ((4 : R) - ((z j).val : R)) * w j

def cyclicHashModeCode
    (p N : ℕ) (i : Fin 3) (u : CyclicModeWord N) :
    Fin 3 → Fin (2 * N) → ZMod p :=
  match i with
  | ⟨0, _⟩ => fun
      | ⟨0, _⟩, j => ((2 * (u.1 j).val : ℕ) : ZMod p)
      | ⟨1, _⟩, j => 4 * (4 - ((u.2.1 j).val : ZMod p))
      | ⟨2, _⟩, j => -2 * ((2 * (u.2.2 j).val : ℕ) : ZMod p)
      | ⟨r + 3, h⟩, _ => absurd h (by omega)
  | ⟨1, _⟩ => fun
      | ⟨0, _⟩, j => ((2 * (u.1 j).val : ℕ) : ZMod p)
      | ⟨1, _⟩, j => -2 * ((2 * (u.2.1 j).val : ℕ) : ZMod p)
      | ⟨2, _⟩, j => 4 * (4 - ((u.2.2 j).val : ZMod p))
      | ⟨r + 3, h⟩, _ => absurd h (by omega)
  | ⟨2, _⟩ => fun
      | ⟨0, _⟩, j => 4 - ((u.1 j).val : ZMod p)
      | ⟨1, _⟩, j => ((2 * (u.2.1 j).val : ℕ) : ZMod p)
      | ⟨2, _⟩, j => ((2 * (u.2.2 j).val : ℕ) : ZMod p)
      | ⟨r + 3, h⟩, _ => absurd h (by omega)
  | ⟨r + 3, h⟩ => absurd h (by omega)

def cyclicAffineHash
    (p N alpha beta gamma delta : ℕ)
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p) (i : Fin 3)
    (e : CyclicAmbientEdge N alpha beta gamma delta) : ZMod p :=
  shift + match i with
  | ⟨0, _⟩ =>
      doubledXHash (2 * offset) (w 0) (e.1.1 0) +
        4 * doubledZHash 0 (w 1) (e.2.1.1 2) -
        2 * doubledYHash offset (w 2) (e.2.2.1 1)
  | ⟨1, _⟩ =>
      doubledYHash (2 * offset) (w 0) (e.1.1 1) -
        2 * doubledXHash 0 (w 1) (e.2.1.1 0) +
        4 * doubledZHash offset (w 2) (e.2.2.1 2)
  | ⟨2, _⟩ =>
      doubledZHash (2 * offset) (w 0) (e.1.1 2) +
        doubledYHash 0 (w 1) (e.2.1.1 1) +
        doubledXHash offset (w 2) (e.2.2.1 0)
  | ⟨r + 3, h⟩ => absurd h (by omega)

end MME.StothersFourth.Phi233


