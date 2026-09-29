-- Prove2me | solution 2 for DiophantineLattice.frac_shortest_isInhomMin
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T01:36:13.693495+00:00
-- url     : https://prove2.me/submissions/918e270a-5b3b-49a7-89b1-ac9d45a210ed

import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap
import Definitions.Def_Novelty_DiophantineLatticeShiftedTheta
import Definitions.Def_Novelty_DiophantineLatticeTorsionGap
open DiophantineLattice Finset in
theorem solution {n : ℕ} {B : Matrix (Fin n) (Fin n) ℚ} (hpd : PosDef B) {lam : ℚ}
    (h : IsMinEnergy B lam) {v : Fin n → ℤ} (hv : form B (emb v) = lam) {r : ℤ} (hr : 2 ≤ r) :
    IsInhomMin B (fracPt v r) (lam / (r : ℚ) ^ 2) := by
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
  obtain ⟨⟨v0, hv0ne, hv0⟩, hmin⟩ := h
  have hlampos : 0 < lam := by
    rw [← hv0]
    exact hpd _ (hembne hv0ne)
  have hembzero : form B (emb (0 : Fin n → ℤ)) = 0 := by
    have e : emb (0 : Fin n → ℤ) = fun _ => (0 : ℚ) := by
      funext i
      simp [emb]
    rw [e]
    exact hzero B
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, hembzero] at hv
    linarith
  have hdouble : ∀ m : Fin n → ℤ, form B (emb (fun j => 2 * m j)) = 4 * form B (emb m) := by
    intro m
    have e : emb (fun j => 2 * m j) = fun i => (2 : ℚ) * emb m i := by
      funext i
      simp only [emb]
      push_cast
      ring
    rw [e, hscale]
    norm_num
  have hprim : ∀ m : Fin n → ℤ, (fun i => v i - 2 * m i) ≠ 0 := by
    intro m h0
    have hvm : v = fun j => 2 * m j := by
      funext j
      have hj := congrFun h0 j
      simp only [Pi.zero_apply] at hj
      omega
    have hmne : m ≠ 0 := by
      intro hm0
      apply hvne
      funext j
      rw [hvm]
      simp [hm0]
    have hle := hmin m hmne
    rw [hvm, hdouble] at hv
    linarith
  have hr0 : (r : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (r : ℚ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hr
    exact ne_of_gt this
  have hrsq : (0 : ℚ) < (r : ℚ) ^ 2 := by positivity
  have hkey : ∀ m : Fin n → ℤ, form B (fun i => fracPt v r i - emb m i)
      = form B (emb (fun j => v j - r * m j)) / (r : ℚ) ^ 2 := by
    intro m
    have e : (fun i => fracPt v r i - emb m i)
        = fun i => (1 / (r : ℚ)) * emb (fun j => v j - r * m j) i := by
      funext i
      simp only [fracPt, emb]
      push_cast
      field_simp
    rw [e, hscale]
    field_simp
  have hrmul : ∀ m : Fin n → ℤ, form B (emb (fun j => r * m j)) = (r : ℚ) ^ 2 * form B (emb m) := by
    intro m
    have e : emb (fun j => r * m j) = fun i => (r : ℚ) * emb m i := by
      funext i
      simp only [emb]
      push_cast
      ring
    rw [e, hscale]
  have hprimr : ∀ m : Fin n → ℤ, (fun i => v i - r * m i) ≠ 0 := by
    intro m h0
    have hvm : v = fun j => r * m j := by
      funext j
      have hj := congrFun h0 j
      simp only [Pi.zero_apply] at hj
      omega
    have hmne : m ≠ 0 := by
      intro hm0
      apply hvne
      funext j
      rw [hvm]
      simp [hm0]
    have hle := hmin m hmne
    rw [hvm, hrmul] at hv
    have h4 : (4 : ℚ) ≤ (r : ℚ) ^ 2 := by
      have : (2 : ℚ) ≤ (r : ℚ) := by exact_mod_cast hr
      nlinarith
    nlinarith
  refine ⟨⟨0, ?_⟩, ?_⟩
  · rw [hkey]
    have e : (fun j => v j - r * (0 : Fin n → ℤ) j) = v := by
      funext j
      simp
    rw [e, hv]
  · intro m
    rw [hkey]
    have hlb := hmin _ (hprimr m)
    gcongr
