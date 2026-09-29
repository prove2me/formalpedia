-- Prove2me | Definitions.Def_Probability_CoxeterLength
-- name    : Probability_CoxeterLength
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:11:40.631279+00:00
-- url     : https://prove2.me/theorems/cc79b661-f7fc-43a2-ab29-3ad53c06b8ee
-- title:
--   Aether Catalog definitions — Probability_CoxeterLength
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.CoxeterLength`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/CoxeterLength.lean by skeleton subtraction
import Mathlib
/-
# Coxeter length on the symmetric group and the sign character

The refinement asked for in Conjecture A speaks of a permutation of *minimal Coxeter length*.
This file supplies the notion and its basic theory in the shape needed there:

* `ParityGap.coxeterLength σ` — the number of inversions of `σ`, i.e. the length of `σ` in the
  Coxeter presentation of the symmetric group by adjacent transpositions;
* `ParityGap.sign_eq_neg_one_pow_coxeterLength` — the sign character is the parity of the
  Coxeter length;
* `ParityGap.coxeterLength_eq_zero_iff` — only the identity has length `0`.
-/


open Equiv Equiv.Perm Finset

namespace ParityGap

variable {n : ℕ}

/-- The inversion set of a permutation of `Fin n`: pairs `x = ⟨x₁, x₂⟩` with `x₂ < x₁` whose
order is reversed by `σ`. -/
def inversions (σ : Perm (Fin n)) : Finset (Σ _ : Fin n, Fin n) :=
  (Equiv.Perm.finPairsLT n).filter (fun x => σ x.1 < σ x.2)

/-- The **Coxeter length** of a permutation: its number of inversions. -/
def coxeterLength (σ : Perm (Fin n)) : ℕ := (inversions σ).card





end ParityGap


