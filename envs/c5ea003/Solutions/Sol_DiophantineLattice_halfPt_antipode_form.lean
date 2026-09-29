-- Prove2me | solution 1 for DiophantineLattice.halfPt_antipode_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T01:20:19.464975+00:00
-- url     : https://prove2.me/submissions/d65433be-aa28-48ed-98d6-ea2249e8944e

import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap
import Definitions.Def_Novelty_DiophantineLatticeShiftedTheta
import Definitions.Def_Novelty_DiophantineLatticeTorsionGap
open DiophantineLattice Finset in
theorem solution {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (v m : Fin n → ℤ) :
    form B (fun i => halfPt v i - emb (fun j => v j - m j) i)
      = form B (fun i => halfPt v i - emb m i) := by
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
  have e : (fun i => halfPt v i - emb (fun j => v j - m j) i)
      = fun i => (-1 : ℚ) * (halfPt v i - emb m i) := by
    funext i
    simp only [halfPt, emb]
    push_cast
    ring
  rw [e, hscale]
  norm_num
