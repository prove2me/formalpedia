-- Prove2me | solution 1 for AlmostLossless.card_bad_seeds
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:36:42.852766+00:00
-- url     : https://prove2.me/submissions/37824a9d-4556-4515-9635-13d7bae4321e

-- Sol generated from Logic/AlmostLossless/ExactPlanar.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_ExactPlanar
import Definitions.Def_Logic_AlmostLossless_Hashing
import Theorems.Thm_AlmostLossless_card_ker_mul_card_eq
import Theorems.Thm_AlmostLossless_eq_zero_of_orth_two
import Theorems.Thm_AlmostLossless_surjective_dotHom

/-!
# The exact failure probability of the planar inner-product compressor

The union bound of `AlmostLossless.collisionProb_le` charges one `1/p` per pair
of typical words.  In dimension `k = 2` the truth is *exactly* computable, and
it is strictly better whenever two pairs of typical words happen to differ by
proportional vectors: only the **projective directions** of the difference set
matter.

For a seed `a ∈ (ZMod p)²` the hash `x ↦ ⟨a,x⟩` confuses `x` and `y` iff `a`
lies on the line orthogonal to `x - y`.  Distinct projective directions give
lines meeting only at the origin, so the bad seeds form a "pencil" of `d` lines
through `0`:

`#{bad seeds} = 1 + d·(p-1)`, i.e. `P(failure) = (1 + d(p-1))/p²`,

where `d` is the number of distinct directions among the differences of typical
words (`AlmostLossless.exact_card_collides_planar`).  Since `d ≤ |T|(|T|-1)/2`,
this refines the union bound, and it is an *equality*, so the falsifiability
gate of the research thread is met with an exact figure rather than a bound.

This is a small bridge between finite projective geometry over `𝔽_p` and the
Monte-Carlo analysis of a compressor.
-/

open AlmostLossless

open Finset


variable {p : ℕ} [Fact p.Prime]

/-! ## Elementary identities for the inner-product hash -/




/-- Each such line has exactly `p` seeds. -/
theorem card_orth {z : Fin 2 → ZMod p} (hz : z ≠ 0) : (orth z).card = p := by
  have h := card_ker_mul_card_eq (dotHom z) (surjective_dotHom hz)
  have hp : Fintype.card (ZMod p) = p := ZMod.card p
  have hcard : Fintype.card (Fin 2 → ZMod p) = p * p := by
    simp [ZMod.card, pow_two]
  rw [hp, hcard] at h
  have hppos : 0 < p := (Fact.out (p := p.Prime)).pos
  exact Nat.eq_of_mul_eq_mul_right hppos h

theorem zero_mem_orth (z : Fin 2 → ZMod p) : (0 : Fin 2 → ZMod p) ∈ orth z := by
  simp [orth, dotHom]


/-! ## The pencil of bad seeds -/


/-! ## Exact failure probability of the planar compressor -/




/-! ## A worked example, cross-checked by exhaustive computation

The hypotheses of `exact_card_collides_planar` are satisfiable: here is a
concrete typical set over `ZMod 11`.  The count predicted by the theorem
(`1 + 3·(11-1) = 31` bad seeds out of `121`) is confirmed independently by
brute-force evaluation, which also shows the theorem is not vacuous. -/










open AlmostLossless in
theorem solution(D : Finset (Fin 2 → ZMod p)) (hD : D.Nonempty)
    (h0 : ∀ z ∈ D, z ≠ 0)
    (hnp : ∀ z ∈ D, ∀ w ∈ D, z ≠ w → z 0 * w 1 - z 1 * w 0 ≠ 0) :
    #{a : Fin 2 → ZMod p | ∃ z ∈ D, dotHom z a = 0} = 1 + D.card * (p - 1) := by
  classical
  have hBeq : ({a : Fin 2 → ZMod p | ∃ z ∈ D, dotHom z a = 0} : Finset _)
      = insert 0 (D.biUnion (fun z => (orth z).erase 0)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_biUnion, Finset.mem_erase, orth]
    constructor
    · rintro ⟨z, hz, hza⟩
      by_cases ha : a = 0
      · exact Or.inl ha
      · exact Or.inr ⟨z, hz, ha, by simpa using hza⟩
    · rintro (rfl | ⟨z, hz, _, hza⟩)
      · obtain ⟨z, hz⟩ := hD
        exact ⟨z, hz, by simp [dotHom]⟩
      · exact ⟨z, hz, by simpa using hza⟩
  have hdisj : ∀ z ∈ D, ∀ w ∈ D, z ≠ w →
      Disjoint ((orth z).erase 0) ((orth w).erase 0) := by
    intro z hz w hw hzw
    rw [Finset.disjoint_left]
    intro a haz haw
    rw [Finset.mem_erase] at haz haw
    have hza : dotHom z a = 0 := by simpa [orth] using haz.2
    have hwa : dotHom w a = 0 := by simpa [orth] using haw.2
    exact haz.1 (eq_zero_of_orth_two (hnp z hz w hw hzw) hza hwa)
  have hcardU : (D.biUnion (fun z => (orth z).erase 0)).card = D.card * (p - 1) := by
    rw [Finset.card_biUnion hdisj]
    have : ∀ z ∈ D, ((orth z).erase 0).card = p - 1 := by
      intro z hz
      rw [Finset.card_erase_of_mem (zero_mem_orth z), card_orth (h0 z hz)]
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]
  have hnotmem : (0 : Fin 2 → ZMod p) ∉ D.biUnion (fun z => (orth z).erase 0) := by
    simp
  rw [hBeq, Finset.card_insert_of_notMem hnotmem, hcardU, Nat.add_comm]
