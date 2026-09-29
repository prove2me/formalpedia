-- Prove2me | solution 1 for Bridges.ResidueLeakage.signVectors_ncard
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:42:25.382572+00:00
-- url     : https://prove2.me/submissions/52cf74a4-6db4-42d4-a428-7dc8fe252c16

-- Sol generated from Bridges/ResidueLeakageCounting.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageCounting
import Definitions.Def_Bridges_ResidueLeakagePatternSurjectivity
import Theorems.Thm_Bridges_ResidueLeakage_signVectors_succ
/-
# Counting the leakage: the fingerprint carries exactly `K` bits

Sixth file of the residue-leakage thread.  `qrFingerprint_range_eq` identifies
the range of the fingerprint on primes with the set of `±1`-vectors of length
`K`.  Here we count that set, so that the leakage curve becomes an exact
number:

`|{ F_A(q) : q prime, q ∉ A }| = 2^K`.

Combined with `dirichlet_no_pruning` this is the quantitative form of the
verdict: the channel emits exactly `K` bits about `N`, and none of them about
the individual factors.
-/


open Bridges.ResidueLeakage


@[simp] theorem signVectors_zero : signVectors 0 = {([] : List ℤ)} := by
  ext v
  simp only [signVectors, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hlen, -⟩; exact List.length_eq_zero_iff.1 hlen
  · rintro rfl; exact ⟨rfl, by simp⟩


theorem signVectors_finite (n : ℕ) : (signVectors n).Finite := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [signVectors_succ]
      exact (ih.image _).union (ih.image _)





open Bridges.ResidueLeakage in
theorem solution(n : ℕ) : (signVectors n).ncard = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hinj1 : Function.Injective (List.cons (1 : ℤ)) := by
        intro a b hab; simpa using hab
      have hinj2 : Function.Injective (List.cons (-1 : ℤ)) := by
        intro a b hab; simpa using hab
      have hdisj : Disjoint (List.cons (1 : ℤ) '' signVectors n)
          (List.cons (-1 : ℤ) '' signVectors n) := by
        rw [Set.disjoint_left]
        rintro v ⟨w, -, rfl⟩ ⟨w', -, hw'⟩
        have : (1 : ℤ) = -1 := by
          have := congrArg (fun l : List ℤ => l.head?) hw'
          simpa using this.symm
        norm_num at this
      rw [signVectors_succ, Set.ncard_union_eq hdisj
        ((signVectors_finite n).image _) ((signVectors_finite n).image _),
        Set.ncard_image_of_injective _ hinj1,
        Set.ncard_image_of_injective _ hinj2, ih]
      ring
