-- Prove2me | solution 2 for DiophantineLattice.halfPt_multiplicity_even
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T01:27:10.759125+00:00
-- url     : https://prove2.me/submissions/ea86bbf3-ad64-4d94-987d-65fdedd332cc

import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap
import Definitions.Def_Novelty_DiophantineLatticeShiftedTheta
import Definitions.Def_Novelty_DiophantineLatticeTorsionGap
open DiophantineLattice Finset in
theorem solution {n : ℕ} {B : Matrix (Fin n) (Fin n) ℚ} (hpd : PosDef B) {lam : ℚ}
    (h : IsMinEnergy B lam) {v : Fin n → ℤ} (hv : form B (emb v) = lam) (c : ℚ)
    (S : Finset (Fin n → ℤ))
    (hS : ∀ m : Fin n → ℤ, m ∈ S ↔ form B (fun i => halfPt v i - emb m i) = c) :
    Even S.card := by
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
  have hanti : ∀ (v m : Fin n → ℤ), form B (fun i => halfPt v i - emb (fun j => v j - m j) i)
      = form B (fun i => halfPt v i - emb m i) := by
    intro v m
    have e : (fun i => halfPt v i - emb (fun j => v j - m j) i)
        = fun i => (-1 : ℚ) * (halfPt v i - emb m i) := by
      funext i
      simp only [halfPt, emb]
      push_cast
      ring
    rw [e, hscale]
    norm_num
  have hv2 := hprim
  have hmem : ∀ m ∈ S, (fun j => v j - m j) ∈ S := by
    intro m hm
    rw [hS] at hm ⊢
    rw [hanti v m]
    exact hm
  have hnefix : ∀ m ∈ S, (fun j => v j - m j) ≠ m := by
    intro m _ h0
    refine hv2 m ?_
    funext j
    have hj := congrFun h0 j
    simp only [Pi.zero_apply]
    omega
  have hinv : ∀ (m : Fin n → ℤ), m ∈ S → (fun j => v j - (fun j => v j - m j) j) = m := by
    intro m _
    funext j
    simp
  have hsum : ∑ _x ∈ S, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (fun m _ => fun j => v j - m j) (fun m _ => by decide)
      (fun m hm _ => hnefix m hm) (fun m hm => hmem m hm) (fun m hm => hinv m hm)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact ZMod.natCast_eq_zero_iff_even.mp hsum
