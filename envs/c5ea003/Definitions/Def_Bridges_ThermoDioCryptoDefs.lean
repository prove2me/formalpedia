-- Prove2me | Definitions.Def_Bridges_ThermoDioCryptoDefs
-- name    : Bridges_ThermoDioCryptoDefs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:40:34.217023+00:00
-- url     : https://prove2.me/theorems/f6ddb3ca-efc4-4595-99e3-cbbc16c4bd7c
-- title:
--   Aether Catalog definitions — Bridges_ThermoDioCryptoDefs
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ThermoDioCryptoDefs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ThermoDioCryptoDefs.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Thermodynamic Diophantine Cryptanalysis: Berggren Transfer Operators
for Certified Security of Triple-Based One-Way Maps.

Bridge: connects thermodynamic formalism to cryptographic security on the Berggren tree.
Keywords: entropy, post_quantum_security, certified_robustness, lattice_crypto, quantum_walk
-/

open Finset Real BigOperators

namespace BerggrenCrypto

/-! ## Berggren Generators

The three Berggren matrices generate the full tree of primitive Pythagorean triples
from the seed (3, 4, 5). We define the corresponding maps on integer triples. -/

/-- First Berggren generator: A-branch of the Pythagorean triple tree. -/
def berggrenA (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (t.1 - 2 * t.2.1 + 2 * t.2.2,
   2 * t.1 - t.2.1 + 2 * t.2.2,
   2 * t.1 - 2 * t.2.1 + 3 * t.2.2)

/-- Second Berggren generator: B-branch of the Pythagorean triple tree. -/
def berggrenB (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (t.1 + 2 * t.2.1 + 2 * t.2.2,
   2 * t.1 + t.2.1 + 2 * t.2.2,
   2 * t.1 + 2 * t.2.1 + 3 * t.2.2)

/-- Third Berggren generator: C-branch of the Pythagorean triple tree. -/
def berggrenC (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (-t.1 + 2 * t.2.1 + 2 * t.2.2,
   -2 * t.1 + t.2.1 + 2 * t.2.2,
   -2 * t.1 + 2 * t.2.1 + 3 * t.2.2)

/-- The three children of a triple under Berggren generation. -/
def berggrenChildren (t : ℤ × ℤ × ℤ) : Finset (ℤ × ℤ × ℤ) :=
  {berggrenA t, berggrenB t, berggrenC t}

/-! ## Finite-Depth Descendants

Cumulative Berggren descendants up to depth `n`, always including the seed.
This forms the finite truncation of the infinite Berggren tree. -/

/-- Cumulative descendants of `seed` under Berggren generation up to depth `n`.
Bridge: finite-depth truncation approximating the infinite thermodynamic boundary. -/
def berggrenDescendants (seed : ℤ × ℤ × ℤ) : ℕ → Finset (ℤ × ℤ × ℤ)
  | 0 => {seed}
  | n + 1 =>
    let prev := berggrenDescendants seed n
    prev ∪ prev.biUnion berggrenChildren




/-! ## Cryptographic Observable Structure

Bridge: connects thermodynamic formalism to cryptographic security.
A crypto observable assigns a nonneg weight to each triple with Lipschitz control. -/


/-! ## Depth Energy and Hash Fiber Indicators

Supporting definitions for the thermodynamic-cryptographic bridge. -/







instance : DecidableEq (ℤ × ℤ × ℤ) := inferInstance

instance berggrenDescendantsFintype (seed : ℤ × ℤ × ℤ) (n : ℕ) :
    Fintype (berggrenDescendants seed n : Set (ℤ × ℤ × ℤ)) :=
  (berggrenDescendants seed n).fintypeCoeSort

instance hashFiberDecidable {m : ℕ} (H : ℤ × ℤ × ℤ → Fin m) (y : Fin m) :
    DecidablePred (fun t => H t = y) :=
  fun t => decEq (H t) y

/-! ## Core Cryptographic Definitions

Partition sums, collision counts, preimage counts, and weighted probabilities. -/











end BerggrenCrypto


