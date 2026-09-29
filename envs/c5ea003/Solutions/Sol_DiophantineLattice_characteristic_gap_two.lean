-- Prove2me | solution 1 for DiophantineLattice.characteristic_gap_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:01:06.442847+00:00
-- url     : https://prove2.me/submissions/c8f8291c-349e-4059-8596-75a399872ea5

import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap
import Definitions.Def_Novelty_DiophantineLatticeCompleteSquare
import Definitions.Def_Novelty_DiophantineLatticeCharacteristic
open DiophantineLattice Finset in
theorem solution {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hsym : ∀ i j, B i j = B j i)
    {v : Fin n → ℤ} (hchar : IsCharacteristic B v) (m m' : Fin n → ℤ)
    (hne : form (toRat B) (fun i => halfPt v i - emb m i)
      ≠ form (toRat B) (fun i => halfPt v i - emb m' i)) :
    2 ≤ |form (toRat B) (fun i => halfPt v i - emb m i)
      - form (toRat B) (fun i => halfPt v i - emb m' i)| := by
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
  have hcastf : ∀ z : Fin n → ℤ, form (toRat B) (emb z) = ((zform B z : ℤ) : ℚ) := by
    intro z
    simp only [form, bil, zform, zbil, toRat, emb, Matrix.map_apply]
    push_cast
    rfl
  have hhalf : ∀ k : Fin n → ℤ, form (toRat B) (fun i => halfPt v i - emb k i)
      = ((zform B (fun j => v j - 2 * k j) : ℤ) : ℚ) / 4 := by
    intro k
    have e : (fun i => halfPt v i - emb k i)
        = fun i => (1 / 2 : ℚ) * emb (fun j => v j - 2 * k j) i := by
      funext i
      simp only [halfPt, emb]
      push_cast
      ring
    rw [e, hscale, hcastf]
    ring
  have hbilsymm : ∀ x y : Fin n → ℤ, zbil B x y = zbil B y x := by
    intro x y
    simp only [zbil]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hsym j i]
    ring
  have hzadd : ∀ x y : Fin n → ℤ, zform B (fun i => x i + y i)
      = zform B x + (zbil B x y + zbil B y x) + zform B y := by
    intro x y
    simp only [zform, zbil]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hzsmul : ∀ (c : ℤ) (x : Fin n → ℤ), zform B (fun i => c * x i) = c ^ 2 * zform B x := by
    intro c x
    simp only [zform, zbil, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hzbilsmul : ∀ (c : ℤ) (x y : Fin n → ℤ), zbil B x (fun i => c * y i) = c * zbil B x y := by
    intro c x y
    simp only [zbil, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hkey : ∀ k : Fin n → ℤ, ∃ s : ℤ, zform B (fun j => v j - 2 * k j) = zform B v + 8 * s := by
    intro k
    obtain ⟨d, hd⟩ := hchar k
    refine ⟨d - zbil B v k, ?_⟩
    have e : (fun j => v j - 2 * k j) = fun j => v j + (-2 : ℤ) * k j := by
      funext j
      ring
    rw [e, hzadd, hbilsymm (fun i => (-2 : ℤ) * k i) v, hzbilsmul, hzsmul]
    linarith [hd]
  obtain ⟨s, hs⟩ := hkey m
  obtain ⟨s', hs'⟩ := hkey m'
  rw [hhalf m, hhalf m', hs, hs']
  have hsne : s ≠ s' := by
    intro h
    apply hne
    rw [hhalf m, hhalf m', hs, hs', h]
  have e2 : ((zform B v + 8 * s : ℤ) : ℚ) / 4 - ((zform B v + 8 * s' : ℤ) : ℚ) / 4
      = 2 * ((s : ℚ) - (s' : ℚ)) := by
    push_cast
    ring
  rw [e2, abs_mul]
  have h1 : (1 : ℚ) ≤ |(s : ℚ) - (s' : ℚ)| := by
    have hz : (1 : ℤ) ≤ |s - s'| := Int.one_le_abs (sub_ne_zero_of_ne hsne)
    calc (1 : ℚ) = ((1 : ℤ) : ℚ) := by norm_num
      _ ≤ ((|s - s'| : ℤ) : ℚ) := by exact_mod_cast hz
      _ = |(s : ℚ) - (s' : ℚ)| := by simp [Int.cast_abs]
  have h2 : |(2 : ℚ)| = 2 := by norm_num
  rw [h2]
  linarith
