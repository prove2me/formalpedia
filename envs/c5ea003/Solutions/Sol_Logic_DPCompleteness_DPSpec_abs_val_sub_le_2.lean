-- Prove2me | solution 2 for Logic.DPCompleteness.DPSpec.abs_val_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:02:18.677799+00:00
-- url     : https://prove2.me/submissions/59dccc94-d4a6-4434-bd07-66fd66498686

import Mathlib
import Definitions.Def_Logic_DPCompleteness
import Definitions.Def_Logic_DPCompletenessStability
open Logic.DPCompleteness in
theorem solution {S W : Type*} [AddCommGroup W] [Fintype S] [Nonempty S] [LinearOrder W]
    [IsOrderedAddMonoid W] {D D' : DPSpec S W} {a b : W}
    (hinit : ∀ s, |D'.init s - D.init s| ≤ a)
    (hstep : ∀ i s t, |D'.step i s t - D.step i s t| ≤ b)
    (n : ℕ) (s : S) : |D'.val n s - D.val n s| ≤ a + n • b := by
  -- a uniform pointwise bound survives taking suprema
  have hsup_abs : ∀ (f g : S → W) (c : W), (∀ i, |f i - g i| ≤ c) →
      |(Finset.univ : Finset S).sup' Finset.univ_nonempty f
        - (Finset.univ : Finset S).sup' Finset.univ_nonempty g| ≤ c := by
    intro f g c h
    refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
    · rw [sub_le_iff_le_add]
      refine Finset.sup'_le _ _ (fun i _ => ?_)
      have h1 : f i ≤ c + g i := sub_le_iff_le_add.mp (abs_sub_le_iff.mp (h i)).1
      refine h1.trans ?_
      gcongr
      exact Finset.le_sup' g (Finset.mem_univ i)
    · rw [sub_le_iff_le_add]
      refine Finset.sup'_le _ _ (fun i _ => ?_)
      have h1 : g i ≤ c + f i := sub_le_iff_le_add.mp (abs_sub_le_iff.mp (h i)).2
      refine h1.trans ?_
      gcongr
      exact Finset.le_sup' f (Finset.mem_univ i)
  induction n generalizing s with
  | zero => simpa using hinit s
  | succ n ih =>
    show |(Finset.univ : Finset S).sup' Finset.univ_nonempty
        (fun u => D'.val n u + D'.step n u s)
      - (Finset.univ : Finset S).sup' Finset.univ_nonempty
        (fun u => D.val n u + D.step n u s)| ≤ a + (n + 1) • b
    refine hsup_abs _ _ _ (fun u => ?_)
    have hrw : (D'.val n u + D'.step n u s) - (D.val n u + D.step n u s)
        = (D'.val n u - D.val n u) + (D'.step n u s - D.step n u s) := by abel
    rw [hrw]
    refine (abs_add_le _ _).trans ?_
    rw [succ_nsmul, ← add_assoc]
    exact add_le_add (ih u) (hstep n u s)
