-- Prove2me | solution 1 for Catalog.Probability.SeedRec.exists_not_routed
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:29:16.665569+00:00
-- url     : https://prove2.me/submissions/45060d74-672c-4033-9500-ebecec6434df

-- Sol generated from Probability/PRNGClassifier.lean
import Mathlib
import Definitions.Def_Probability_PRNGClassifier
import Definitions.Def_Probability_PRNGLCGFingerprint
import Definitions.Def_Probability_PRNGLFSRDetection
import Theorems.Thm_Catalog_Probability_SeedRec_card_lcgWords_le
import Theorems.Thm_Catalog_Probability_SeedRec_card_lfsrWords_le

/-!
# Finite-state periodicity and the limits of a seed-compression router

Two structural results about the classifier that routes a file to
*seed-compressible* or *model-compressible*.

**Positive side (why seed compression works at all).**  Any deterministic
generator with a finite state space is eventually periodic with preperiod plus
period at most `|S|`.  Hence its output stream — however long the file — is
completely determined by its first `|S|` symbols: `PRNG.stream_eq_early`.  This
is the structural reason a recovered seed reproduces the file exactly.

**Negative side (why the router cannot be a universal compressor).**  Combining
the counting bounds of the LFSR and LCG files: the union of the two families
covers at most `|K|^{2L} + |K|³` files of length `n`, so as soon as `n` exceeds
`2L` and `3` by a little, most files are rejected by *both* detectors:
`exists_not_routed`.  A seed-compression front end therefore never beats the
pigeonhole bound; it only reallocates code space.

Main contents.

* `PRNG.exists_iterate_collision` — pigeonhole on the state trajectory.
* `PRNG.exists_eventually_periodic` — preperiod `i` and period `p` with
  `i + p ≤ |S|`.
* `PRNG.stream_add_period_mul`, `PRNG.stream_eq_mod` — reduction of any time
  index into the fundamental window.
* `PRNG.stream_eq_early` — the whole stream is determined by its first `|S|`
  symbols.
* `routerWords`, `card_routerWords_le`, `exists_not_routed` — the two-family
  classifier still covers an exponentially small fraction of files.
-/

open Catalog.Probability.SeedRec

variable {S : Type*} {α : Type*} [Fintype S]



variable (g : PRNG S α) (s : S)





variable (K : Type*) [CommRing K] [Fintype K] [DecidableEq K] (L : ℕ)


theorem card_routerWords_le (n : ℕ) :
    (routerWords K L n).card ≤ Fintype.card K ^ (2 * L) + Fintype.card K ^ 3 :=
  (Finset.card_union_le _ _).trans
    (Nat.add_le_add (card_lfsrWords_le K L n) (card_lcgWords_le K n))




open Catalog.Probability.SeedRec in
theorem solution(n : ℕ) (hK : 2 ≤ Fintype.card K)
    (hL : 2 * L + 2 ≤ n) (hn : 5 ≤ n) :
    ∃ x : Fin n → K, x ∉ lfsrWords K L n ∧ x ∉ lcgWords K n := by
  set q := Fintype.card K with hq
  have h1 : q ^ (2 * L) ≤ q ^ (n - 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : q ^ 3 ≤ q ^ (n - 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 2 * q ^ (n - 2) ≤ q ^ (n - 1) := by
    have : q ^ (n - 1) = q * q ^ (n - 2) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [this]
    exact Nat.mul_le_mul_right _ hK
  have h4 : q ^ (n - 1) < q ^ n := Nat.pow_lt_pow_right (by omega) (by omega)
  have hcov : q ^ (2 * L) + q ^ 3 < q ^ n := by omega
  by_contra hc
  push_neg at hc
  have hsub : (Finset.univ : Finset (Fin n → K)) ⊆ routerWords K L n := by
    intro x _
    rw [routerWords, Finset.mem_union]
    by_cases hx : x ∈ lfsrWords K L n
    · exact Or.inl hx
    · exact Or.inr (hc x hx)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at hcard
  have hle := hcard.trans (card_routerWords_le K L n)
  rw [← hq] at hle
  omega
