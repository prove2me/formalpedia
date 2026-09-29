-- Prove2me | solution 1 for TraceSetFilter.card_sqrtSet_le_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:45:57.387434+00:00
-- url     : https://prove2.me/submissions/65663e76-f0f6-4625-ba96-b7a8a819feb5

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




@[simp] theorem mem_sqrtSet {N x : K} : x ∈ sqrtSet N ↔ x ^ 2 = N := by simp [sqrtSet]

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
theorem solution(N : K) : (sqrtSet N).card ≤ 2 := by
  classical
  by_cases h : ∃ r : K, r ^ 2 = N
  · obtain ⟨r, hr⟩ := h
    have : sqrtSet N ⊆ ({r, -r} : Finset K) := by
      intro x hx
      rw [mem_sqrtSet] at hx
      have : (x - r) * (x + r) = 0 := by linear_combination hx - hr
      rcases mul_eq_zero.1 this with h1 | h1
      · simp [sub_eq_zero.1 h1]
      · simp [eq_neg_of_add_eq_zero_left h1]
    exact le_trans (card_le_card this) (card_insert_le _ _ |>.trans (by simp))
  · have : sqrtSet N = ∅ := by
      ext x; simp only [mem_sqrtSet, notMem_empty, iff_false]
      intro hx; exact h ⟨x, hx⟩
    simp [this]
