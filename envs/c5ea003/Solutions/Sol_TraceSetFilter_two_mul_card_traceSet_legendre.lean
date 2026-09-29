-- Prove2me | solution 1 for TraceSetFilter.two_mul_card_traceSet_legendre
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:12:01.677235+00:00
-- url     : https://prove2.me/submissions/e30fa4ff-a7da-4dd0-a6d2-0292fd224e03

-- Sol generated from Applications/TraceSetFilter.lean
import Mathlib
import Definitions.Def_Applications_TraceSetFilter
import Theorems.Thm_TraceSetFilter_two_mul_card_traceSet
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
theorem solution(hm : m ≠ 2) (N : ℤ) (hN : ((N : ZMod m)) ≠ 0) :
    2 * ((traceSet ((N : ZMod m))).card : ℤ) = m + legendreSym m N := by
  have h := two_mul_card_traceSet hN
  have hcard : Fintype.card (ZMod m) = m := ZMod.card m
  have hroots : ((sqrtSet ((N : ZMod m))).card : ℤ) = legendreSym m N + 1 := by
    rw [← legendreSym.card_sqrts (p := m) hm N]
    congr 2
    ext x
    simp [sqrtSet]
  have hm1 : 1 ≤ m := (Fact.out : Nat.Prime m).one_lt.le.trans' (by norm_num)
  have := congrArg (fun k : ℕ => (k : ℤ)) h
  push_cast [hcard, Nat.cast_sub hm1] at this
  rw [this, hroots]
  ring
