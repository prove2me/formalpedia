-- Prove2me | solution 1 for DiophantineLattice.form_sub_emb_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T02:13:54.332285+00:00
-- url     : https://prove2.me/submissions/fc1329e3-22dc-4ab0-9b0d-917982753de5

import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap
import Definitions.Def_Novelty_DiophantineLatticeExactOrder
open DiophantineLattice Finset in
theorem solution {n : ℕ} {B : Matrix (Fin n) (Fin n) ℚ} (hpd : PosDef B) (k m : Fin n → ℤ) :
    form B (fun i => emb k i - emb m i) = 0 ↔ m = k := by
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
  have hsubemb : ∀ (k m : Fin n → ℤ), (fun i => emb k i - emb m i) = emb (fun j => k j - m j) := by
    intro k m
    funext i
    simp only [emb]
    push_cast
    ring
  have hzeroiff : ∀ (k m : Fin n → ℤ), form B (fun i => emb k i - emb m i) = 0 ↔ m = k := by
    intro k m
    rw [hsubemb]
    constructor
    · intro h0
      by_contra hne
      have hne' : (fun j => k j - m j) ≠ 0 := by
        intro he
        apply hne
        funext j
        have hj := congrFun he j
        simp only [Pi.zero_apply] at hj
        omega
      have hpos := hpd _ (hembne hne')
      linarith
    · intro h
      subst h
      have e : (fun j => m j - m j) = (0 : Fin n → ℤ) := by
        funext j
        simp
      have e2 : emb (0 : Fin n → ℤ) = fun _ => (0 : ℚ) := by
        funext i
        simp [emb]
      rw [e, e2]
      exact hzero B
  exact hzeroiff k m
