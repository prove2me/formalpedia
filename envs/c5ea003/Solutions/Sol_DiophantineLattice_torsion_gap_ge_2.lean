-- Prove2me | solution 2 for DiophantineLattice.torsion_gap_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T01:45:45.608431+00:00
-- url     : https://prove2.me/submissions/e95665b8-98a9-403c-ab51-deee53343e5d

import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap
import Definitions.Def_Novelty_DiophantineLatticeShiftedTheta
import Definitions.Def_Novelty_DiophantineLatticeTorsionGap
open DiophantineLattice Finset in
theorem solution {n : ℕ} {B : Matrix (Fin n) (Fin n) ℚ} {lam : ℚ}
    (hmin : ∀ m : Fin n → ℤ, m ≠ 0 → lam ≤ form B (emb m)) {v : Fin n → ℤ} {r : ℤ} (hr : r ≠ 0)
    (hnot : ∀ m : Fin n → ℤ, (fun i => v i - r * m i) ≠ 0) (m : Fin n → ℤ) :
    lam / (r : ℚ) ^ 2 ≤ form B (fun i => fracPt v r i - emb m i) := by
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
  have hr0 : (r : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hr
  have hrsq : (0 : ℚ) < (r : ℚ) ^ 2 := by positivity
  have hkey : form B (fun i => fracPt v r i - emb m i)
      = form B (emb (fun j => v j - r * m j)) / (r : ℚ) ^ 2 := by
    have e : (fun i => fracPt v r i - emb m i)
        = fun i => (1 / (r : ℚ)) * emb (fun j => v j - r * m j) i := by
      funext i
      simp only [fracPt, emb]
      push_cast
      field_simp
    rw [e, hscale]
    field_simp
  rw [hkey]
  have hlb := hmin _ (hnot m)
  gcongr
