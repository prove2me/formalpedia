-- Prove2me | Theorems.Thm_TraceSetFilter_factor_of_disc_square
-- name    : TraceSetFilter.factor_of_disc_square
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:06:45.306762+00:00
-- url     : https://prove2.me/theorems/306ce461-de3e-44fe-bb65-c4aee21abc27
-- title:
--   The concrete Fermat step: a square discriminant hands over the factorisation
-- statement:
--   The concrete Fermat step: a square discriminant hands over the factorisation
--   explicitly.
--
--   ```lean
--   theorem TraceSetFilter.factor_of_disc_square{N s d : ℤ} (hd : d ^ 2 = s ^ 2 - 4 * N) :
--       ((s - d) / 2) * ((s + d) / 2) = N ∧ (s - d) / 2 + (s + d) / 2 = s := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/TraceSetFilter.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/TraceSetFilter.lean#L326

-- Thm stub generated from Applications/TraceSetFilter.lean
import Mathlib
import Definitions.Def_Applications_TraceSetFilter
/-
# The trace-set filter: exact, but exactly half-sized

Let `N = p·q` be a semiprime and let `s = p + q` be its **trace**.  Fermat's
method scans candidate traces `s`; the *trace-set filter* (TRACEPROFILE) is the
free consistency test

  `s` is admissible mod `m`  ⟺  `s mod m ∈ T_m(N) := { x + N/x : x ∈ (ℤ/m)ˣ }`.

This file develops the exact theory of `T_m(N)` over an arbitrary finite field
(so in particular over `ZMod m` for a prime `m ∤ N`) and proves the facts that
the experimental round measured numerically:

* `TraceSetFilter.add_mem_traceSet` — **exactness / zero false negatives**: the
  true trace of *any* factorisation `a·b = N` lies in the trace set.  Hence the
  filter never rejects the truth (the measured `400/400` survival).
* `TraceSetFilter.mem_traceSet_iff_isSquare` — the filter is precisely the
  Fermat discriminant test: `t ∈ T` iff `t² − 4N` is a square.
* `TraceSetFilter.two_mul_card_traceSet` — **exact `2^{-1}` pruning per prime**:
  `2·|T| = (|K| − 1) + #{x : x² = N}`, hence `|K| − 1 ≤ 2|T| ≤ |K| + 1`.  A wrong
  candidate survives with probability `(1 ± 1/m)/2`: exactly the measured
  `0.1233 ≈ 2⁻³` and `0.0151 ≈ 2⁻⁶`.
* `TraceSetFilter.factorResidueSet_eq_nonzero` — the **`p`-filter is empty**: the
  set of admissible factor residues mod `m` is *all* of `(ℤ/m)ˣ`, so the filter
  only re-tests coprimality (measured survival `1.0000`).
* `TraceSetFilter.two_mul_card_traceSet_legendre` — the same count with its
  exact Legendre correction: `2·|T| = m + χ(N)`.
* `TraceSetFilter.card_ge_of_exact_filter` — **minimality**: the trace set is
  contained in every *exact* filter, so no residue-local consistency test can
  prune a wrong candidate by more than (essentially) one bit per prime.
* `TraceSetFilter.exists_factorisation_iff_isSquare_int` — **the `s`-scan is
  Fermat in disguise**: over `ℤ`, `s` is the trace of a factorisation of `N`
  iff `s² − 4N` is a perfect square.

Companion file: `Catalog/Applications/TraceSetNoAmplification.lean`, which
multiplies these local densities through the Chinese remainder theorem and shows
that the filter cannot amplify an interval hint.
-/

open TraceSetFilter

open Finset

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-! ## The trace set of `N` in a finite field -/





/-! ## Exactness: no false negatives -/



/-! ## The fibres of the trace map -/


/-! ## The Fermat discriminant description -/


/-! ## The exact size of the filter -/





/-! ## Minimality: no exact residue filter can do better -/



/-! ## Specialisation: prime moduli and semiprimes -/


variable {m : ℕ} [Fact (Nat.Prime m)]





/-! ## The `s`-scan is Fermat in disguise -/

theorem TraceSetFilter.factor_of_disc_square{N s d : ℤ} (hd : d ^ 2 = s ^ 2 - 4 * N) :
    ((s - d) / 2) * ((s + d) / 2) = N ∧ (s - d) / 2 + (s + d) / 2 = s := by sorry
