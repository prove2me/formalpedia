-- Prove2me | Theorems.Thm_Round7Agreement_mem_agree_iff_jacobiSym
-- name    : Round7Agreement.mem_agree_iff_jacobiSym
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:37:57.211146+00:00
-- url     : https://prove2.me/theorems/c7f35866-59cf-49aa-9491-c0cf3e1b237d
-- title:
--   The aggregate is `N`-computable.
-- statement:
--   **The aggregate is `N`-computable.** Agreement holds exactly when the Jacobi
--   symbol `J(a | N)` — a quantity computable from `N` alone — equals `1`.
--
--   ```lean
--   theorem Round7Agreement.mem_agree_iff_jacobiSym(a : (ZMod (p * q))ˣ) :
--       a ∈ agree p q ↔ jacobiSym ((a : ZMod (p * q)).val : ℤ) (p * q) = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/Round7AgreementCharacter.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/Round7AgreementCharacter.lean#L217

-- Thm stub generated from Tropical/Round7AgreementCharacter.lean
import Mathlib
import Definitions.Def_Tropical_Round7AgreementCharacter

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

open Round7Agreement

open Finset

variable {p q : ℕ}


variable [Fact p.Prime] [Fact q.Prime]













/-! ## The agreement set -/




/-! ## A CRT witness: non-residue mod `p`, trivial mod `q` -/


variable [Fact p.Prime] [Fact q.Prime]



/-! ## The count -/


variable [Fact p.Prime] [Fact q.Prime]





/-! ## The collapse onto the Jacobi symbol -/


variable [Fact p.Prime] [Fact q.Prime]

theorem Round7Agreement.mem_agree_iff_jacobiSym(a : (ZMod (p * q))ˣ) :
    a ∈ agree p q ↔ jacobiSym ((a : ZMod (p * q)).val : ℤ) (p * q) = 1 := by sorry
