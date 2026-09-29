-- Prove2me | solution 1 for mme_released_global_uniform_tolerance_window_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:31:04.66096+00:00
-- url     : https://prove2.me/submissions/6a0b4d58-62d9-4bb9-b437-306d5283f3dd

import Definitions.Def_mme_released_global_frame_data
import Definitions.Def_mme_global_CW_joint_start_data
import Theorems.Thm_mme_released_global_joint_counts_valid
import Theorems.Thm_mme_released_global_supported_frame
import Theorems.Thm_mme_released_global_uniform_window_bounds
import Theorems.Thm_mme_global_CW_histogram_window_cofinal_extraction
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.ReleasedGlobal MME.MoreAsymmetryExactSeed MME.GlobalCW MME.RegionRate MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
universe u
attribute [local irreducible] jointRows alpha atom rowCounts jointCounts coarseCounts wordCounts shapeEquiv

/-- One outer extraction scale threshold works for every positive histogram
tolerance below a fixed bound, retaining the complete source restriction
and logarithmic copy estimate. -/
theorem solution {K : Type u} [Field K] (owner : Fin 6) (rho : ℝ)
    (hrho : 0 ≤ rho) (hgap : rho < (profile owner).rate (fun _ ↦ 1)) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∃ k0 : ℕ,
      ∀ eps : ℝ, 0 < eps → eps ≤ eps0 → ∀ k : ℕ, k0 ≤ k →
      ∃ hk : 0 < k^2, ∃ a : Reference owner (k^2),
      ∃ S : GlobalCW.Part (4*blocks (k^2)) 3
        ((frame owner (k^2) hk a).window (windowGood owner (k^2) eps)),
        1 ≤ S.inputs ∧ S.inputs ≤ (blocks (k^2)+1)^10935 ∧
        rho*(blocks (k^2) : ℝ) + Real.log (S.inputs : ℝ) ≤ S.rate ∧
        Restrict (bigAdd (fun _ : Fin ⌈Real.exp S.rate⌉₊ ↦ tensor K
          ((frame owner (k^2) hk a).window (windowGood owner (k^2) eps))))
          (bigAdd (fun _ : Fin S.inputs ↦ tensor K (fun _ (_ : FineWord (4*blocks (k^2))) ↦ True))) := by
  let delta := ((profile owner).rate (fun _ ↦ 1)-rho)/2
  have hd : 0 < delta := by dsimp [delta]; linarith
  obtain ⟨eps0,heps0,hwindow⟩ := mme_released_global_uniform_window_bounds owner delta hd
  let E := (denominator : ℝ)^5*((profile owner).rate (fun _ ↦ 1)-delta)
  let J := massEntropy ((profile owner).1 0) - (profile owner).rate (fun _ ↦ 1)+delta
  let B := (denominator : ℝ)^5*|J|
  have hden : (0 : ℝ) < (denominator : ℝ)^5 := by norm_num [denominator]
  have hB : 0 ≤ B := mul_nonneg hden.le (abs_nonneg _)
  have hR : 0 ≤ (denominator : ℝ)^5*rho := mul_nonneg hden.le hrho
  have hE : (denominator : ℝ)^5*rho < E := by
    apply mul_lt_mul_of_pos_left _ hden
    dsimp [delta]
    linarith
  obtain ⟨k0,hk0⟩ := mme_global_CW_histogram_window_cofinal_extraction
    (K := K) (4*denominator^5) 8 10935 B E ((denominator : ℝ)^5*rho) hB hR hE
  refine ⟨eps0, heps0, k0, ?_⟩
  intro eps heps heps0bound k hk
  obtain ⟨hk1,hextract⟩ := hk0 k hk
  have hk2 : 0 < k^2 := pow_pos (by omega) _
  obtain ⟨a,_,hne⟩ := mme_released_global_supported_frame owner (k^2) hk2
  let D := frame owner (k^2) hk2 a
  have h45 : Fintype.card Shape = 45 := mme_released_global_joint_counts_valid.2.2.1
  have h81 : Fintype.card Word = 81 := mme_released_global_joint_counts_valid.2.2.2.1
  have hc : Fintype.card (Cell 8 1 (fun _ _ ↦ 8)) = 45 := by
    rw [Fintype.card_sigma]
    simpa only [Fin.sum_univ_one] using h45
  have uniform (mu : D.AdmissibleProfile) (hgood : ∀ i, windowGood owner (k^2) eps i (mu.val i)) :=
    hwindow (k^2) hk2 a k hk1 mu
      (fun i c w ↦ (hgood i c w).trans heps0bound)
  have hlow (mu : D.AdmissibleProfile) (hg : ∀ i, windowGood owner (k^2) eps i (mu.val i)) :
      E*(k : ℝ)^2 ≤ (D.stage mu k hk1).entropyRate := by
    convert (uniform mu hg).1 using 1 <;> dsimp [E,blocks] <;> push_cast <;> ring
  have hupp (mu : D.AdmissibleProfile) (hg : ∀ i, windowGood owner (k^2) eps i (mu.val i)) :
      (D.stage mu k hk1).entropyExponent ≤ B*(k : ℝ)^2 := by
    apply (uniform mu hg).2.trans
    calc
      (blocks (k^2) : ℝ)*J ≤ (blocks (k^2) : ℝ)*|J| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ = B*(k : ℝ)^2 := by dsimp [B,blocks]; push_cast; ring
  obtain ⟨S,hi,hpoly,hr,ht⟩ := hextract D (windowGood owner (k^2) eps) (hne eps heps.le)
    (by apply le_of_eq; dsimp [blocks]; ring) (by rfl)
    (by change Fintype.card (Cell 8 1 (fun _ _ ↦ 8)) ≤ 10935; omega)
    (by change 1*(8+1) ≤ 10935; norm_num)
    (by change 1*(8+1)*Fintype.card Word ≤ 10935; rw [h81]; norm_num)
    (by change 3*Fintype.card (Cell 8 1 (fun _ _ ↦ 8))*Fintype.card Word ≤ 10935; rw [hc,h81] <;> norm_num)
    hlow hupp
  refine ⟨hk2,a,S,hi,?_,?_,ht⟩
  · simpa only [show D.L = blocks (k^2) from rfl,
      show Fintype.card (Cell D.degree D.R D.bounds) = 45 from hc,
      show Fintype.card (CompleteSplit.CompleteWord 3) = 81 from h81] using hpoly
  · convert hr using 1 <;> dsimp [blocks] <;> push_cast <;> ring


#print axioms solution
