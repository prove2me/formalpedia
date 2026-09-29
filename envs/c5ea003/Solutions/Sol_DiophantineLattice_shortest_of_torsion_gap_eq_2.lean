-- Prove2me | solution 2 for DiophantineLattice.shortest_of_torsion_gap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T02:35:17.194233+00:00
-- url     : https://prove2.me/submissions/fd40065d-9a07-4239-80b3-2ee3c69cc98b

import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap
import Definitions.Def_Novelty_DiophantineLatticeExactOrder
import Definitions.Def_Novelty_DiophantineLatticeTorsionGap
open DiophantineLattice Finset in
theorem solution {n : ℕ} {B : Matrix (Fin n) (Fin n) ℚ} {lam : ℚ} {t : Fin n → ℚ}
    {r : ℤ} (hr : r ≠ 0) (ht : IsTorsionShift t r)
    (hgap : IsInhomMin B t (lam / (r : ℚ) ^ 2)) :
    ∃ w k : Fin n → ℤ, form B (emb w) = lam ∧ ∀ i, t i = (w i : ℚ) / (r : ℚ) + (k i : ℚ) := by
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
  obtain ⟨⟨u, hu⟩, -⟩ := ht
  obtain ⟨⟨m0, hm0⟩, -⟩ := hgap
  have hteq : t = fracPt u r := by
    funext i
    have hi := hu i
    simp only [fracPt]
    field_simp
    linarith [hi]
  rw [hteq, hfrac B u m0 hr] at hm0
  refine ⟨(fun j => u j - r * m0 j), m0, ?_, ?_⟩
  · have h4 : form B (emb fun j => u j - r * m0 j) = lam := by
      field_simp at hm0
      linarith [hm0]
    exact h4
  · intro i
    have hi := hu i
    rw [hteq]
    simp only [fracPt]
    push_cast
    field_simp
    linarith [hi]
