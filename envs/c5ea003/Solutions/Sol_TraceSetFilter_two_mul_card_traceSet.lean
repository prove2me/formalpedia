-- Prove2me | solution 1 for TraceSetFilter.two_mul_card_traceSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:48:21.803348+00:00
-- url     : https://prove2.me/submissions/4b67ca9b-0161-4d77-b54f-54ba615a2d85

-- Sol generated from Applications/TraceSetFilter.lean
import Mathlib
import Definitions.Def_Applications_TraceSetFilter
import Theorems.Thm_TraceSetFilter_traceMap_eq_iff
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



@[simp] theorem mem_traceSet {N t : K} : t ∈ traceSet N ↔ ∃ x : K, x ≠ 0 ∧ x + N / x = t := by
  simp [traceSet, and_comm]

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
theorem solution{N : K} (hN : N ≠ 0) :
    2 * (traceSet N).card = (Fintype.card K - 1) + (sqrtSet N).card := by
  classical
  set S : Finset K := univ.erase (0 : K) with hS
  set R : Finset K := sqrtSet N with hR
  set T := traceSet N with hT
  have hSc : S.card = Fintype.card K - 1 := by
    rw [hS, card_erase_of_mem (mem_univ _), card_univ]
  have hmapS : ∀ x ∈ S, (fun x => x + N / x) x ∈ T := fun x hx => mem_image_of_mem _ hx
  have hRS : ∀ x ∈ R, x ∈ S := by
    intro x hx
    rw [hR, mem_sqrtSet] at hx
    simp only [hS, mem_erase, mem_univ, and_true]
    rintro rfl
    exact hN (by simpa using hx.symm)
  have hmapR : ∀ x ∈ R, (fun x => x + N / x) x ∈ T := fun x hx => hmapS x (hRS x hx)
  have e1 := Finset.card_eq_sum_card_fiberwise hmapS
  have e2 := Finset.card_eq_sum_card_fiberwise hmapR
  have key : ∀ t ∈ T, (S.filter (fun x => x + N / x = t)).card
      + (R.filter (fun x => x + N / x = t)).card = 2 := by
    intro t ht
    obtain ⟨x, hx, hfx⟩ := mem_traceSet.1 ht
    have hNx : N / x ≠ 0 := div_ne_zero hN hx
    have hfibS : S.filter (fun y => y + N / y = t) = ({x, N / x} : Finset K) := by
      ext y
      simp only [hS, mem_filter, mem_erase, mem_univ, and_true, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hy0, hy⟩
        exact (traceMap_eq_iff hx hy0).1 (hfx.trans hy.symm)
      · rintro (rfl | rfl)
        · exact ⟨hx, hfx⟩
        · refine ⟨hNx, ?_⟩
          rw [← hfx]
          exact ((traceMap_eq_iff hx hNx).2 (Or.inr rfl)).symm
    by_cases hsq : x ^ 2 = N
    · have hxx : N / x = x := by rw [div_eq_iff hx]; linear_combination -hsq
      have hfibR : R.filter (fun y => y + N / y = t) = ({x} : Finset K) := by
        ext y
        simp only [hR, mem_filter, mem_sqrtSet, mem_singleton]
        constructor
        · rintro ⟨hy2, hy⟩
          have hy0 : y ≠ 0 := by rintro rfl; simp at hy2; exact hN hy2.symm
          rcases (traceMap_eq_iff hx hy0).1 (hfx.trans hy.symm) with h | h
          · exact h
          · rw [h, hxx]
        · rintro rfl; exact ⟨hsq, hfx⟩
      rw [hfibS, hfibR, hxx]
      simp
    · have hxx : N / x ≠ x := by
        intro h; exact hsq (by rw [div_eq_iff hx] at h; linear_combination -h)
      have hfibR : R.filter (fun y => y + N / y = t) = (∅ : Finset K) := by
        ext y
        simp only [hR, mem_filter, mem_sqrtSet, notMem_empty, iff_false, not_and]
        intro hy2 hy
        have hy0 : y ≠ 0 := by rintro rfl; simp at hy2; exact hN hy2.symm
        rcases (traceMap_eq_iff hx hy0).1 (hfx.trans hy.symm) with h | h
        · exact hsq (by rw [← h]; exact hy2)
        · have hxy : y * x = N := by rw [h]; field_simp
          have hz : y * (x - y) = 0 := by linear_combination hxy - hy2
          rcases mul_eq_zero.1 hz with h1 | h1
          · exact hy0 h1
          · exact hsq (by rw [sub_eq_zero.1 h1]; exact hy2)
      rw [hfibS, hfibR, card_pair (Ne.symm hxx)]
      simp
  calc 2 * T.card = ∑ _t ∈ T, 2 := by rw [sum_const, smul_eq_mul, mul_comm]
    _ = ∑ t ∈ T, ((S.filter (fun x => x + N / x = t)).card
          + (R.filter (fun x => x + N / x = t)).card) := (sum_congr rfl key).symm
    _ = S.card + R.card := by rw [sum_add_distrib, ← e1, ← e2]
    _ = (Fintype.card K - 1) + R.card := by rw [hSc]
