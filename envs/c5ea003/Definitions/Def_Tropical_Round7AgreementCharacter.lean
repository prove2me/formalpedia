-- Prove2me | Definitions.Def_Tropical_Round7AgreementCharacter
-- name    : Tropical_Round7AgreementCharacter
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:29.006097+00:00
-- url     : https://prove2.me/theorems/c9304b9b-13ab-4d3f-a0ae-6c0ee8a7a233
-- title:
--   Aether Catalog definitions — Tropical_Round7AgreementCharacter
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.Round7AgreementCharacter`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/Round7AgreementCharacter.lean by skeleton subtraction
import Mathlib

/-!
# Round-7 closure AGREEMENT: barrier-2-invariant character aggregates collapse

This file formalises experiment 325 of the round-7 batch.  For a semiprime
`N = p q` the **agreement set**

`A(N) = { a ∈ (ℤ/Nℤ)ˣ : (a/p) = (a/q) }`

is invariant under both barrier-2 symmetries (the swap `p ↔ q` and conjugation),
so it was a candidate for a factor-revealing aggregate that escapes the
residue/order classification.  It does not:

* `agree_card_two_mul` : `2 · |A(N)| = φ(N)`, i.e. `A(N) = φ(N)/2` exactly, for
  every semiprime with an odd prime factor — the count is a *function of `N`
  alone* (through `φ(N)`), hence carries no information about `p` and `q`;
* `mem_agree_iff_jacobiSym` : the agreement set *is* the set where the
  `N`-computable Jacobi symbol `J(a | N)` equals `1`, so the aggregate collapses
  onto the quadratic character mod `N` by character orthogonality.

The proof is a pairing argument: an element `u` that is a non-residue mod `p`
and `≡ 1 (mod q)` (produced by CRT) translates the agreement set bijectively
onto its complement.
-/

namespace Round7Agreement

open Finset

variable {p q : ℕ}

section Chars

variable [Fact p.Prime] [Fact q.Prime]

/-- Reduction `ℤ/pqℤ → ℤ/pℤ`. -/
def redP (p q : ℕ) : ZMod (p * q) →+* ZMod p := ZMod.castHom ⟨q, rfl⟩ (ZMod p)

/-- Reduction `ℤ/pqℤ → ℤ/qℤ`. -/
def redQ (p q : ℕ) : ZMod (p * q) →+* ZMod q := ZMod.castHom ⟨p, mul_comm p q⟩ (ZMod q)

/-- The Legendre character mod `p`, read on the units of `ℤ/pqℤ`. -/
noncomputable def chiP (p q : ℕ) [Fact p.Prime] (a : (ZMod (p * q))ˣ) : ℤ :=
  quadraticChar (ZMod p) (redP p q (a : ZMod (p * q)))

/-- The Legendre character mod `q`, read on the units of `ℤ/pqℤ`. -/
noncomputable def chiQ (p q : ℕ) [Fact q.Prime] (a : (ZMod (p * q))ˣ) : ℤ :=
  quadraticChar (ZMod q) (redQ p q (a : ZMod (p * q)))









/-! ## The agreement set -/

/-- The agreement set `A(N) = {a : (a/p) = (a/q)}`. -/
noncomputable def agree (p q : ℕ) [Fact p.Prime] [Fact q.Prime] :
    Finset ((ZMod (p * q))ˣ) :=
  Finset.univ.filter (fun a => chiP p q a = chiQ p q a)


end Chars

/-! ## A CRT witness: non-residue mod `p`, trivial mod `q` -/

section Witness

variable [Fact p.Prime] [Fact q.Prime]


end Witness

/-! ## The count -/

section Count

variable [Fact p.Prime] [Fact q.Prime]




end Count

/-! ## The collapse onto the Jacobi symbol -/

section Jacobi

variable [Fact p.Prime] [Fact q.Prime]




end Jacobi

end Round7Agreement


