-- Prove2me | solution 1 for mme_released_global_simultaneous_uniform_window_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:50:39.465981+00:00
-- url     : https://prove2.me/submissions/e4ac9746-99af-461a-ac05-61ce833d2ecc

import Theorems.Thm_mme_released_global_uniform_tolerance_window_extraction
import Mathlib.Data.Finset.Lattice.Fold

open BigOperators MME MME.TensorObj MME.ProfiledCW MME.ReleasedGlobal
  MME.MoreAsymmetryExactSeed MME.GlobalCW
universe u

/-- All six outer extractions share a positive tolerance bound and a scale threshold. -/
theorem solution
    {K : Type u} [Field K] (rho : Fin 6 → ℝ)
    (hrho : ∀ owner, 0 ≤ rho owner)
    (hgap : ∀ owner, rho owner < (profile owner).rate (fun _ ↦ 1)) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∃ k0 : ℕ,
      ∀ eps : ℝ, 0 < eps → eps ≤ eps0 → ∀ k : ℕ, k0 ≤ k →
      ∀ owner : Fin 6,
      ∃ hk : 0 < k^2, ∃ a : Reference owner (k^2),
      ∃ S : GlobalCW.Part (4*blocks (k^2)) 3
        ((frame owner (k^2) hk a).window (windowGood owner (k^2) eps)),
        1 ≤ S.inputs ∧ S.inputs ≤ (blocks (k^2)+1)^10935 ∧
        rho owner*(blocks (k^2) : ℝ) + Real.log (S.inputs : ℝ) ≤ S.rate ∧
        Restrict (bigAdd (fun _ : Fin ⌈Real.exp S.rate⌉₊ ↦ tensor K
          ((frame owner (k^2) hk a).window (windowGood owner (k^2) eps))))
          (bigAdd (fun _ : Fin S.inputs ↦ tensor K (fun _ (_ : FineWord (4*blocks (k^2))) ↦ True))) := by
  classical
  have houter := fun owner =>
    mme_released_global_uniform_tolerance_window_extraction
      (K := K) owner (rho owner) (hrho owner) (hgap owner)
  choose eps0 heps0 k0 houter using houter
  refine ⟨Finset.univ.inf' Finset.univ_nonempty eps0, ?_, Finset.univ.sup k0, ?_⟩
  · exact (Finset.lt_inf'_iff _).mpr (fun owner _ => heps0 owner)
  · intro eps heps hepsbound k hk owner
    exact houter owner eps heps
      (hepsbound.trans (Finset.inf'_le eps0 (Finset.mem_univ owner))) k
      ((Finset.le_sup (Finset.mem_univ owner)).trans hk)


#print axioms solution
