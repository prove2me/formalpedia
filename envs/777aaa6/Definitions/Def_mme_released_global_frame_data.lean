-- Prove2me | Definitions.Def_mme_released_global_frame_data
-- name    : mme_released_global_frame_data
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-22T11:19:57.068983+00:00
-- url     : https://prove2.me/theorems/96b69194-dc34-41af-9fb1-ab80dd84400a
-- title:
--   Scaled global frames and windows for the concrete candidate
-- statement:
--   Original global block positions, scaled exact histograms, actual HistogramFrame data from a coarse reference address, and a frequency tolerance window about the fixed concrete real profile.
-- source:
--   Concrete released-profile realization for the unpaired global stage of More Asymmetry Theorem 5.3.

import Definitions.Def_mme_released_global_profile_data
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed MME.GlobalCW MME.RecursiveYZ
set_option autoImplicit false
namespace MME.ReleasedGlobal

def blocks (k : ℕ) : ℕ := denominator^5*k

noncomputable def counts (owner : Fin 6) (k : ℕ) (_ : Fin 1) (c : Shape) : ℕ :=
  k*coarseCounts owner c

abbrev Reference (owner : Fin 6) (k : ℕ) :=
  {a : RecursiveXHash.Address 8 1 (fun _ _ ↦ 8) (fun _ ↦ blocks k) //
    a ∈ RecursiveXHash.target (counts owner k)}

def positions (k : ℕ) : Fin (blocks k) ≃ Place (fun _ : Fin 1 ↦ blocks k) where
  toFun := fun t ↦ ⟨0,t⟩
  invFun := fun p ↦ p.2
  left_inv := fun _ ↦ rfl
  right_inv := by rintro ⟨r,t⟩; have h : r = 0 := Fin.eq_zero r; subst r; rfl

noncomputable def frame (owner : Fin 6) (k : ℕ) (hk : 0 < k)
    (a : Reference owner k) : HistogramFrame 3 (4*blocks k) where
  degree := 8
  R := 1
  bounds := fun _ _ ↦ 8
  n := fun _ ↦ blocks k
  m := counts owner k
  N := blocks k - 1
  hashPositions := (finCongr (Nat.sub_add_cancel
    (by
      have hb : 0 < blocks k := by unfold blocks denominator; positivity
      omega))).trans (positions k)
  degree_eq := by norm_num
  L := blocks k
  positions := positions k
  length := by norm_num; omega
  reference := a.val
  reference_target := a.property

noncomputable def scaledWords (owner : Fin 6) (k : ℕ) :
    Fin 3 → Cell 8 1 (fun _ _ ↦ 8) → Word → ℕ :=
  fun i c w ↦ k*wordCounts owner i c.2 w

/-- The concrete frequency window around the reconstructed global profile. -/
noncomputable def windowGood (owner : Fin 6) (k : ℕ) (eps : ℝ)
    (i : Fin 3) (mu : Cell 8 1 (fun _ _ ↦ 8) → Word → ℕ) : Prop :=
  ∀ c w, |(mu c w : ℝ)/(blocks k : ℝ) - (profile owner).2 i c w| ≤ eps

end MME.ReleasedGlobal


