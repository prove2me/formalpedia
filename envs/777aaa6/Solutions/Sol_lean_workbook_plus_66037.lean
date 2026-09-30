-- Prove2me | solution 1 for lean_workbook_plus_66037
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:44:25.181301+00:00
-- url     : https://prove2.me/submissions/53d41b9d-7a12-44c6-8eb5-9a0c2285de5c

import Mathlib.NumberTheory.Divisors
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum

def product400Triples : Finset (ℕ × ℕ × ℕ) :=
  (Nat.divisorsAntidiagonal 400).biUnion fun p =>
    (Nat.divisorsAntidiagonal p.2).image fun q => (p.1, q.1, q.2)

theorem product400_triples_membership (x y z : ℕ) :
    (x, y, z) ∈ product400Triples ↔ x * y * z = 400 := by
  simp only [product400Triples, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hab, ⟨⟨c, d⟩, hcd, heq⟩⟩
    have h1 : a * b = 400 := (Nat.mem_divisorsAntidiagonal.mp hab).1
    have h2 : c * d = b := (Nat.mem_divisorsAntidiagonal.mp hcd).1
    have ht : a = x ∧ c = y ∧ d = z := by simpa using heq
    rcases ht with ⟨rfl, rfl, rfl⟩
    rw [Nat.mul_assoc, h2]
    exact h1
  · intro h
    refine ⟨(x, y * z), ?_, (y, z), ?_, rfl⟩
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨by simpa [Nat.mul_assoc] using h, by decide⟩
    · refine Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, ?_⟩
      intro hz
      change y * z = 0 at hz
      rw [Nat.mul_assoc, hz, Nat.mul_zero] at h
      norm_num at h

theorem product400_enumeration_card : product400Triples.card = 90 := by decide

theorem product400_triple_count :
    Nat.card {t : ℕ × ℕ × ℕ // t.1 * t.2.1 * t.2.2 = 400} = 90 := by
  rw [Nat.subtype_card product400Triples (fun ⟨x, y, z⟩ => product400_triples_membership x y z)]
  exact product400_enumeration_card

theorem solution (x y z : ℕ) (h : x * y * z = 400) :
    x * y * z = 400 ∧ x > 0 ∧ y > 0 ∧ z > 0 := by
  refine ⟨h, ?_, ?_, ?_⟩
  · by_contra hx
    have hx0 : x = 0 := by omega
    simp [hx0] at h
  · by_contra hy
    have hy0 : y = 0 := by omega
    simp [hy0] at h
  · by_contra hz
    have hz0 : z = 0 := by omega
    simp [hz0] at h
