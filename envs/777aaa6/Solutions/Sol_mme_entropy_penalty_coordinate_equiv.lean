-- Prove2me | solution 1 for mme_entropy_penalty_coordinate_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T11:44:58.750984+00:00
-- url     : https://prove2.me/submissions/8b80322d-ae61-445f-9410-9ba3b3753bad

import Definitions.Def_mme_recursive_split_coordinate_data

open scoped BigOperators
open MME.RecursiveThinSplit

/-- Relabeling the three physical modes preserves the maximum-entropy penalty.
Both the feasible marginal distributions and their entropies are transported. -/
theorem solution
    {half : ℕ} (parent : Fin 3 → ℕ) (p : Equiv.Perm (Fin 3))
    (alpha : Split half parent → ℝ) :
    entropyPenalty (fun c => alpha ((coordinateEquiv parent p).symm c)) =
      entropyPenalty alpha := by
  classical
  let e := coordinateEquiv (half := half) parent p
  have he (q : Split half (fun i => parent (p i)) → ℝ) :
      mme_modern_entropyBits (fun c => q (e c)) = mme_modern_entropyBits q := by
    unfold mme_modern_entropyBits
    rw [Equiv.sum_comp e (fun c => Real.negMulLog (q c))]
  have hm (q : Split half (fun i => parent (p i)) → ℝ)
      (i : Fin 3) (j : Fin (half + 1)) :
      mme_modern_marginal (fun c : Split half parent => c.val (p i))
        (fun c => q (e c)) j =
      mme_modern_marginal (fun c : Split half (fun i => parent (p i)) => c.val i)
        q j := by
    let f : {c : Split half parent // c.val (p i) = j} ≃
        {c : Split half (fun i => parent (p i)) // c.val i = j} :=
      Equiv.subtypeEquiv e (fun c => Iff.rfl)
    exact Equiv.sum_comp f (fun c => q c.val)
  have hs (q : Split half (fun i => parent (p i)) → ℝ) :
      q ∈ SameMarginalDistributions (fun c => alpha (e.symm c)) ↔
        (fun c => q (e c)) ∈ SameMarginalDistributions alpha := by
    constructor
    · rintro ⟨hpos, hsum, hmargin⟩
      refine ⟨fun c => hpos (e c), ?_, ?_⟩
      · exact (Equiv.sum_comp e q).trans hsum
      · intro i j
        have h := hmargin (p.symm i) j
        rw [← hm q (p.symm i) j,
          ← hm (fun c => alpha (e.symm c)) (p.symm i) j] at h
        simpa only [p.apply_symm_apply, e.symm_apply_apply] using h
    · rintro ⟨hpos, hsum, hmargin⟩
      refine ⟨?_, ?_, ?_⟩
      · intro c
        simpa only [e.apply_symm_apply] using hpos (e.symm c)
      · exact (Equiv.sum_comp e q).symm.trans hsum
      · intro i j
        rw [← hm q i j, ← hm (fun c => alpha (e.symm c)) i j]
        simpa only [e.symm_apply_apply] using hmargin (p i) j
  have himage :
      mme_modern_entropyBits '' SameMarginalDistributions (fun c => alpha (e.symm c)) =
        mme_modern_entropyBits '' SameMarginalDistributions alpha := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨fun c => q (e c), (hs q).mp hq, he q⟩
    · rintro ⟨q, hq, rfl⟩
      refine ⟨fun c => q (e.symm c), ?_, ?_⟩
      · apply (hs _).mpr
        simpa only [e.symm_apply_apply] using hq
      · have h := he (fun c => q (e.symm c))
        simpa only [e.symm_apply_apply] using h.symm
  have halpha : mme_modern_entropyBits (fun c => alpha (e.symm c)) =
      mme_modern_entropyBits alpha := by
    have h := he (fun c => alpha (e.symm c))
    simpa only [e.symm_apply_apply] using h.symm
  change sSup (mme_modern_entropyBits '' SameMarginalDistributions
    (fun c => alpha (e.symm c))) - mme_modern_entropyBits (fun c => alpha (e.symm c)) = _
  rw [himage, halpha]
  rfl


#print axioms solution
