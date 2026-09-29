-- Prove2me | Theorems.Thm_ParityGap_coxeterLength_eq_zero_iff
-- name    : ParityGap.coxeterLength_eq_zero_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:46:25.75326+00:00
-- url     : https://prove2.me/theorems/fb9470b4-0e50-4a1f-8a69-b74fc75054a7
-- title:
--   Only the identity permutation has no inversions.
-- statement:
--   Only the identity permutation has no inversions.
--
--   ```lean
--   theorem ParityGap.coxeterLength_eq_zero_iff{σ : Perm (Fin n)} : coxeterLength σ = 0 ↔ σ = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/CoxeterLength.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/CoxeterLength.lean#L55

-- Thm stub generated from Probability/CoxeterLength.lean
import Mathlib
import Definitions.Def_Probability_CoxeterLength
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

open ParityGap

variable {n : ℕ}

theorem ParityGap.coxeterLength_eq_zero_iff{σ : Perm (Fin n)} : coxeterLength σ = 0 ↔ σ = 1 := by sorry
