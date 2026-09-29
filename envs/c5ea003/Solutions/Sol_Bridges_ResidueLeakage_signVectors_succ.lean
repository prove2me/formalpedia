-- Prove2me | solution 1 for Bridges.ResidueLeakage.signVectors_succ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:40:34.959335+00:00
-- url     : https://prove2.me/submissions/38789cab-78dc-43b5-9237-189ad9721fee

-- Sol generated from Bridges/ResidueLeakageCounting.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageCounting
import Definitions.Def_Bridges_ResidueLeakagePatternSurjectivity
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









open Bridges.ResidueLeakage in
theorem solution(n : ℕ) :
    signVectors (n + 1) =
      (List.cons 1 '' signVectors n) ∪ (List.cons (-1) '' signVectors n) := by
  ext v
  constructor
  · rintro ⟨hlen, hv⟩
    obtain ⟨x, w, rfl⟩ : ∃ x w, v = x :: w := by
      cases v with
      | nil => simp at hlen
      | cons x w => exact ⟨x, w, rfl⟩
    have hw : w ∈ signVectors n :=
      ⟨by simpa using hlen, fun y hy => hv y (List.mem_cons_of_mem _ hy)⟩
    rcases hv x (by simp) with hx | hx
    · exact Or.inl ⟨w, hw, by rw [hx]⟩
    · exact Or.inr ⟨w, hw, by rw [hx]⟩
  · rintro (⟨w, ⟨hlen, hw⟩, rfl⟩ | ⟨w, ⟨hlen, hw⟩, rfl⟩) <;>
      refine ⟨by simpa using hlen, ?_⟩ <;> intro y hy <;>
      rcases List.mem_cons.1 hy with rfl | hy
    · exact Or.inl rfl
    · exact hw y hy
    · exact Or.inr rfl
    · exact hw y hy
