-- Prove2me | solution 1 for lean_workbook_plus_33583
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:47:49.355275+00:00
-- url     : https://prove2.me/submissions/aadd9351-b8c0-46d2-ae6d-f6e5b5a7d9d5

import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.NormNum

def integerProduct216Triples : Finset (ℤ × ℤ × ℤ) :=
  (Int.divisorsAntidiag 216).biUnion fun p =>
    (Int.divisorsAntidiag p.2).image fun q => (p.1, q.1, q.2)

theorem integer_product216_membership (a b c : ℤ) :
    (a, b, c) ∈ integerProduct216Triples ↔ a * b * c = 216 := by
  simp only [integerProduct216Triples, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨⟨x, y⟩, hxy, ⟨⟨z, w⟩, hzw, heq⟩⟩
    have h1 : x * y = 216 := (Int.mem_divisorsAntidiag.mp hxy).1
    have h2 : z * w = y := (Int.mem_divisorsAntidiag.mp hzw).1
    have ht : x = a ∧ z = b ∧ w = c := by simpa using heq
    rcases ht with ⟨rfl, rfl, rfl⟩
    rw [mul_assoc, h2]
    exact h1
  · intro h
    refine ⟨(a, b * c), ?_, (b, c), ?_, rfl⟩
    · exact Int.mem_divisorsAntidiag.mpr ⟨by simpa [mul_assoc] using h, by decide⟩
    · refine Int.mem_divisorsAntidiag.mpr ⟨rfl, ?_⟩
      intro hz
      change b * c = 0 at hz
      rw [mul_assoc, hz, mul_zero] at h
      norm_num at h

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem product216_sum19_enumeration :
    integerProduct216Triples.filter (fun t => t.1 + t.2.1 + t.2.2 = 19) =
      {(4, 6, 9), (4, 9, 6), (6, 4, 9), (6, 9, 4), (9, 4, 6), (9, 6, 4)} := by
  decide

theorem product216_sum19_classification (a b c : ℤ) :
    (a * b * c = 216 ∧ a + b + c = 19) ↔
      (a, b, c) ∈ ({(4, 6, 9), (4, 9, 6), (6, 4, 9),
        (6, 9, 4), (9, 4, 6), (9, 6, 4)} : Finset (ℤ × ℤ × ℤ)) := by
  rw [← product216_sum19_enumeration, Finset.mem_filter, integer_product216_membership]

theorem solution : ∃ a b c : ℤ, a * b * c = 216 ∧ a + b + c = 19 := by
  exact ⟨4, 6, 9, (product216_sum19_classification 4 6 9).mpr (by decide)⟩
