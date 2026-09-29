-- Prove2me | solution 2 for DiophantineLattice.torsion_shift_second_gap
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T02:40:22.870442+00:00
-- url     : https://prove2.me/submissions/ec5f24d9-a84c-49c0-ae07-527654e91239

import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap
import Definitions.Def_Novelty_DiophantineLatticeExactOrder
import Definitions.Def_Novelty_DiophantineLatticeTorsionGap
open DiophantineLattice Finset in
theorem solution {n : ℕ} {B : Matrix (Fin n) (Fin n) ℚ} {lam lam2 : ℚ}
    (hmin : ∀ m : Fin n → ℤ, m ≠ 0 → lam ≤ form B (emb m))
    (hlam2 : ∀ w : Fin n → ℤ, lam < form B (emb w) → lam2 ≤ form B (emb w))
    {t : Fin n → ℚ} {r : ℤ} (hr : r ≠ 0) (ht : IsTorsionShift t r) {mu : ℚ}
    (hmu : IsInhomMin B t mu)
    (hne : ¬ ∃ w k : Fin n → ℤ, form B (emb w) = lam ∧
      ∀ i, t i = (w i : ℚ) / (r : ℚ) + (k i : ℚ)) :
    lam2 / (r : ℚ) ^ 2 ≤ mu := by
  have hscale : ∀ (B : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) (x : Fin n → ℚ),
      form B (fun i => c * x i) = c ^ 2 * form B x := by
    intro B c x
    simp only [form, bil, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hzero : ∀ B : Matrix (Fin n) (Fin n) ℚ, form B (fun _ => (0 : ℚ)) = 0 := by
    intro B
    simp [form, bil]
  have hembz : ∀ m : Fin n → ℤ, emb m = 0 → m = 0 := by
    intro m hm
    funext i
    have := congrFun hm i
    simp only [emb, Pi.zero_apply] at this
    exact_mod_cast this
  have hembne : ∀ {m : Fin n → ℤ}, m ≠ 0 → emb m ≠ 0 := by
    intro m h he
    exact h (hembz m he)
  have hfrac : ∀ (B : Matrix (Fin n) (Fin n) ℚ) (v m : Fin n → ℤ) {r : ℤ}, r ≠ 0 →
      form B (fun i => fracPt v r i - emb m i)
        = form B (emb fun j => v j - r * m j) / (r : ℚ) ^ 2 := by
    intro B v m r hr
    have hr0 : (r : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hr
    have e : (fun i => fracPt v r i - emb m i)
        = fun i => (1 / (r : ℚ)) * emb (fun j => v j - r * m j) i := by
      funext i
      simp only [fracPt, emb]
      push_cast
      field_simp
    rw [e, hscale]
    field_simp
  have hr0 : (r : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hr
  have hrsq : (0 : ℚ) < (r : ℚ) ^ 2 := by positivity
  obtain ⟨⟨u, hu⟩, hnotlat⟩ := ht
  obtain ⟨⟨m0, hm0⟩, -⟩ := hmu
  have hteq : t = fracPt u r := by
    funext i
    have hi := hu i
    simp only [fracPt]
    field_simp
    linarith [hi]
  have hcoord : ∀ (m : Fin n → ℤ) (i : Fin n),
      t i = (((fun j => u j - r * m j) i : ℤ) : ℚ) / (r : ℚ) + (m i : ℚ) := by
    intro m i
    have hi := hu i
    rw [hteq]
    simp only [fracPt]
    push_cast
    field_simp
    linarith [hi]
  rw [hteq, hfrac B u m0 hr] at hm0
  have hwne : (fun j => u j - r * m0 j) ≠ 0 := by
    intro h0
    refine hnotlat m0 ?_
    funext i
    have hi := congrFun h0 i
    simp only [Pi.zero_apply] at hi
    have h2 := hcoord m0 i
    rw [hteq] at h2 ⊢
    simp only [fracPt] at h2 ⊢
    simp only [emb]
    rw [h2]
    simp only [hi]
    push_cast
    ring
  have hlow := hmin _ hwne
  have hnelam : form B (emb fun j => u j - r * m0 j) ≠ lam := by
    intro heq
    exact hne ⟨(fun j => u j - r * m0 j), m0, heq, fun i => hcoord m0 i⟩
  have hgt : lam < form B (emb fun j => u j - r * m0 j) := lt_of_le_of_ne hlow (Ne.symm hnelam)
  have h2 := hlam2 _ hgt
  rw [← hm0]
  gcongr
