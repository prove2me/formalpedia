-- Prove2me | solution 1 for TraceSetFilter.exists_factorisation_iff_isSquare_int
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:45:57.826793+00:00
-- url     : https://prove2.me/submissions/26285b2c-f15d-4817-9691-987a64d1b561

-- Sol generated from Applications/TraceSetFilter.lean
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



/-! ## Lab notes: a kernel-verified census for `N = 3233 = 61 · 53`

The following three facts are checked by the kernel (`decide`) and match the
brute-force census recorded in `ComputationalEvidence.md`:

* `|T_13(3233)| = 7 = (13 + 1)/2` (here `χ(N) = +1`);
* `|T_17(3233)| = 8 = (17 − 1)/2` (here `χ(N) = −1`);
* the true trace `61 + 53 = 114` survives the filter mod `13`.
-/

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩





open TraceSetFilter in
theorem solution(N s : ℤ) :
    (∃ a b : ℤ, a * b = N ∧ a + b = s) ↔ ∃ d : ℤ, d ^ 2 = s ^ 2 - 4 * N := by
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨a - b, by linear_combination -4 * hab⟩
  · rintro ⟨d, hd⟩
    have h4 : (s - d) * (s + d) = 4 * N := by linear_combination -hd
    rcases Int.even_or_odd (s - d) with ⟨c, hc⟩ | ⟨c, hc⟩
    · refine ⟨c, s - c, ?_, by ring⟩
      have hd' : d = s - 2 * c := by omega
      subst hd'
      nlinarith [h4]
    · exfalso
      have hodd1 : ¬ (2 ∣ (s - d)) := by omega
      have hodd2 : ¬ (2 ∣ (s + d)) := by omega
      have h2 : (2 : ℤ) ∣ (s - d) * (s + d) := ⟨2 * N, by rw [h4]; ring⟩
      rcases Int.prime_two.2.2 _ _ h2 with h | h
      · exact hodd1 h
      · exact hodd2 h
