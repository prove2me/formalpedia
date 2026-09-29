-- Prove2me | solution 1 for GraphLinearNotation.adjCode_injective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T11:20:20.312796+00:00
-- url     : https://prove2.me/submissions/ff62e2b0-5953-4b5a-bc25-0ee3b96778ee

import Mathlib
import Definitions.Def_Probability_GraphLinearNotation
open GraphLinearNotation Finset in
theorem solution {n : ℕ} : Function.Injective (adjCode : SimpleGraph (Fin n) → ℕ) := by
  classical
  -- the bit position `i·n + j` is injective on `Fin n × Fin n`
  have hpos : ∀ a b : Fin n × Fin n, a.1.val * n + a.2.val = b.1.val * n + b.2.val → a = b := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simp only at h
    have hj := j.isLt
    have hj' := j'.isLt
    rcases lt_trichotomy i.val i'.val with h1 | h1 | h1
    · have := Nat.mul_le_mul_right n (h1 : i.val + 1 ≤ i'.val)
      rw [Nat.succ_mul] at this
      omega
    · have hjj : j.val = j'.val := by rw [h1] at h; omega
      exact Prod.ext (Fin.ext h1) (Fin.ext hjj)
    · have := Nat.mul_le_mul_right n (h1 : i'.val + 1 ≤ i.val)
      rw [Nat.succ_mul] at this
      omega
  -- the code is the binary number whose set bits are the adjacent positions
  let T : SimpleGraph (Fin n) → Finset ℕ := fun G =>
    (univ.filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).image (fun p => p.1.val * n + p.2.val)
  have hcode : ∀ G : SimpleGraph (Fin n), adjCode G = ∑ k ∈ T G, 2 ^ k := by
    intro G
    rw [sum_image (fun a _ b _ h => hpos a b h), sum_filter, adjCode, ← Fintype.sum_prod_type']
    refine sum_congr rfl (fun p _ => ?_)
    unfold adjBit
    split_ifs <;> simp
  have hmem : ∀ (G : SimpleGraph (Fin n)) (i j : Fin n), i.val * n + j.val ∈ T G ↔ G.Adj i j := by
    intro G i j
    constructor
    · intro h
      obtain ⟨p, hp, hpe⟩ := mem_image.mp h
      have := hpos p (i, j) hpe
      subst this
      exact (mem_filter.mp hp).2
    · intro h
      exact mem_image_of_mem (fun p : Fin n × Fin n => p.1.val * n + p.2.val)
        (mem_filter.mpr ⟨mem_univ (i, j), h⟩)
  intro G H hGH
  have hT : T G = T H := by
    rw [hcode G, hcode H] at hGH
    rw [← Finset.toFinset_bitIndices_sum_two_pow (T G), hGH, Finset.toFinset_bitIndices_sum_two_pow]
  ext i j
  rw [← hmem G i j, ← hmem H i j, hT]
