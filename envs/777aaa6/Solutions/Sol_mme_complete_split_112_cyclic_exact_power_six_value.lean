-- Prove2me | solution 1 for mme_complete_split_112_cyclic_exact_power_six_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-20T14:19:48.872619+00:00
-- url     : https://prove2.me/submissions/169573b7-776b-432e-bac9-bdf0347f0c68

import Definitions.Def_mme_complete_split_112_canonical_source_data
import Definitions.Def_mme_complete_split_112_coupled_grading_data
import Theorems.Thm_mme_complete_split_112_canonical_profile_router
import Theorems.Thm_mme_complete_split_112_coupled_restricted_family_certificate
import Theorems.Thm_mme_Ctensor_one_H_one_outer_family_six_finite_extraction
import Theorems.Thm_mme_Ctensor_one_half_family_to_six_finite_rate_of_capacity
import Theorems.Thm_mme_complete_split_112_cyclic_canonical_directional_rates
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_sixSymmetrization_isomorphic_cyclic_orbit
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_modern_entropy_data
import Mathlib.Tactic

/-!
# The cyclic square-112 family on the exact three-mode power

Same chain as the accepted `mme_complete_split_112_cyclic_prescribedZ_six_value`, stopping one
restriction earlier: the matrix family is extracted into the six-symmetrization of the rotated
*exact-profile* power, and the final forgetting step into the prescribed Z power is omitted.
-/

open MME MME.CompleteSplit MME.CompleteSplit112
open CoupledCTensorPackaging
open MME.DWZComponentRestriction MME.DWZRestrictedValue Module
open scoped BigOperators NNReal
open Filter

universe u

set_option autoImplicit false

private theorem restrict_trans
    {K : Type u} [Field K] {d : ℕ}
    {X Y Z : TensorObj K d}
    (hXY : TensorObj.Restrict X Y) (hYZ : TensorObj.Restrict Y Z) :
    TensorObj.Restrict X Z := by
  rcases hXY with ⟨f, hf⟩
  rcases hYZ with ⟨g, hg⟩
  refine ⟨fun i ↦ f i ∘ₗ g i, ?_⟩
  rw [PiTensorProduct.map_comp]
  change PiTensorProduct.map f (PiTensorProduct.map g Z.t) = X.t
  rw [hg, hf]

private def familyCertificate_of_restrict
    {K : Type u} [Field K] {source target : TensorObj K 3}
    {A H volume : ℕ}
    (c : CTensorOneHOneFamilyCertificate source A H volume)
    (h : TensorObj.Restrict source target) :
    CTensorOneHOneFamilyCertificate target A H volume where
  star := c.star
  restrict := restrict_trans c.restrict h
  certificate := c.certificate

private theorem capacity_from_log_rates
    (N A H volume : ℕ) (tau E S delta : ℝ)
    (hN : 0 < N) (hA : 0 < A) (hH : 0 < H)
    (hlogA : ((2 * N : ℕ) : ℝ) * (E - delta) ≤ Real.log (A : ℝ))
    (hlogAH : ((2 * N : ℕ) : ℝ) * (Real.log 2 - delta) ≤
      Real.log ((A : ℝ) * (H : ℝ)))
    (hlogVolume : Real.log (volume : ℝ) / ((2 * N : ℕ) : ℝ) = S)
    (hvolume : 0 < volume) :
    Real.exp (E + 2 * Real.log 2 + 3 * tau * S - 3 * delta) ^ (2 * N) ≤
      (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
        ((((volume ^ 3 : ℕ) : ℝ)) ^ tau) := by
  have hAc : 0 < (A : ℝ) := by exact_mod_cast hA
  have hHc : 0 < (H : ℝ) := by exact_mod_cast hH
  have hVc : 0 < (volume : ℝ) := by exact_mod_cast hvolume
  have hNc : 0 < (((2 * N : ℕ) : ℝ)) := by positivity
  have hlogV : Real.log (volume : ℝ) = ((2 * N : ℕ) : ℝ) * S := by
    simpa [mul_comm] using (div_eq_iff hNc.ne').mp hlogVolume
  rw [← Real.exp_nat_mul]
  have hcap : 0 <
      (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
        ((((volume ^ 3 : ℕ) : ℝ)) ^ tau) := by positivity
  rw [← Real.exp_log hcap]
  rw [Real.exp_le_exp]
  rw [Real.log_mul (by positivity :
      (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) ≠ 0)
      (by positivity : ((((volume ^ 3 : ℕ) : ℝ)) ^ tau) ≠ 0)]
  rw [Real.log_mul (by positivity : (((A ^ 3 : ℕ) : ℝ) ≠ 0))
      (by positivity : ((H : ℝ) ^ 2 ≠ 0))]
  rw [Real.log_rpow (by positivity : 0 < (((volume ^ 3 : ℕ) : ℝ))) tau]
  simp only [Nat.cast_pow, Nat.cast_mul] at hlogAH ⊢
  rw [Real.log_mul hAc.ne' hHc.ne'] at hlogAH
  rw [Real.log_pow, Real.log_pow, Real.log_pow]
  rw [hlogV]
  have hcomb := add_le_add hlogA
    (mul_le_mul_of_nonneg_left hlogAH (by norm_num : (0 : ℝ) ≤ 2))
  norm_num [Nat.cast_mul] at hcomb ⊢
  calc
    (2 : ℝ) * (N : ℝ) *
          (E + 2 * Real.log 2 + 3 * tau * S - 3 * delta) =
        ((2 * (N : ℝ) * (E - delta) +
          2 * (2 * (N : ℝ) * (Real.log 2 - delta))) +
          tau * (3 * (2 * (N : ℝ) * S))) := by ring
    _ ≤ (Real.log (A : ℝ) +
          2 * (Real.log (A : ℝ) + Real.log (H : ℝ))) +
          tau * (3 * (2 * (N : ℝ) * S)) := by
      exact add_le_add hcomb (le_refl _)
    _ = (3 : ℝ) * Real.log (A : ℝ) +
          (2 : ℝ) * Real.log (H : ℝ) +
          tau * ((3 : ℝ) * (2 * (N : ℝ) * S)) := by ring

private theorem sqrt_loss_absorption
    (c : ℕ) (hc : 0 < c) (gap : ℝ) (hgap : 0 < gap) :
    ∀ᶠ m : ℕ in atTop,
      400 * Real.sqrt ((((c * m) + 1 : ℕ) : ℝ)) ≤
        2 * (((c * m : ℕ) : ℝ)) * gap := by
  obtain ⟨M, hM⟩ := exists_nat_gt (80000 / gap ^ 2)
  filter_upwards [eventually_ge_atTop (max M 1)] with m hm
  have hmM : M ≤ m := le_trans (le_max_left M 1) hm
  have hm1 : 1 ≤ m := le_trans (le_max_right M 1) hm
  have hmpos : 0 < m := Nat.zero_lt_of_lt hm1
  have hcmpos : 0 < c * m := Nat.mul_pos hc hmpos
  have hcm1 : 1 ≤ c * m := hcmpos
  have hcastM : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmM
  have hc1 : 1 ≤ c := hc
  have hmcm : m ≤ c * m := by
    simpa [one_mul m] using Nat.mul_le_mul_right m hc1
  have hcastmcm : (m : ℝ) ≤ ((c * m : ℕ) : ℝ) := by
    exact_mod_cast hmcm
  have hgap2 : 0 < gap ^ 2 := sq_pos_of_pos hgap
  have hlarge : 80000 < (((c * m : ℕ) : ℝ)) * gap ^ 2 := by
    have hM' : 80000 / gap ^ 2 < (M : ℝ) := by exact_mod_cast hM
    have hdiv : 80000 / gap ^ 2 < (((c * m : ℕ) : ℝ)) :=
      lt_of_lt_of_le hM' (hcastM.trans hcastmcm)
    exact (div_lt_iff₀ hgap2).mp hdiv
  have hNnonneg : 0 ≤ (((c * m : ℕ) : ℝ)) := by positivity
  have hN1 : (1 : ℝ) ≤ (((c * m : ℕ) : ℝ)) := by exact_mod_cast hcm1
  have hsqrt : 0 ≤ Real.sqrt ((((c * m) + 1 : ℕ) : ℝ)) :=
    Real.sqrt_nonneg _
  have hsqrt_sq :
      Real.sqrt ((((c * m) + 1 : ℕ) : ℝ)) ^ 2 =
        (((c * m) + 1 : ℕ) : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hright : 0 ≤ 2 * (((c * m : ℕ) : ℝ)) * gap := by positivity
  have hscaled := mul_lt_mul_of_pos_left hlarge
    (show 0 < 4 * (((c * m : ℕ) : ℝ)) by positivity)
  have hlinear :
      160000 * ((((c * m) + 1 : ℕ) : ℝ)) ≤
        320000 * (((c * m : ℕ) : ℝ)) := by
    norm_num [Nat.cast_add, Nat.cast_mul] at hN1 ⊢
    nlinarith
  have hsquares :
      (400 * Real.sqrt ((((c * m) + 1 : ℕ) : ℝ))) ^ 2 ≤
        (2 * (((c * m : ℕ) : ℝ)) * gap) ^ 2 := by
    rw [mul_pow, hsqrt_sq]
    nlinarith
  nlinarith [sq_nonneg
    (400 * Real.sqrt ((((c * m) + 1 : ℕ) : ℝ)) +
      2 * (((c * m : ℕ) : ℝ)) * gap)]

private theorem strict_base_absorb
    (W rateLog : ℝ) (hW : 0 < W)
    (N : ℕ) (delta : ℝ)
    (hdeltaGap : 6 * delta ≤ rateLog - 3 * Real.log W)
    (hsqrt :
      400 * Real.sqrt ((((N + 1 : ℕ) : ℝ))) ≤
        2 * (N : ℝ) * (rateLog - 3 * Real.log W)) :
    W ^ (12 * N) ≤
      Real.exp (rateLog - 3 * delta) ^ (4 * N) *
      Real.exp (-400 * Real.sqrt ((((N + 1 : ℕ) : ℝ))) ) := by
  rw [← Real.exp_log hW]
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  rw [Real.exp_le_exp]
  push_cast
  push_cast at hsqrt
  nlinarith

private theorem square112_volume_log_rate
    (l g m : ℕ) (hlg : 0 < l + g) (hm : 0 < m)
    (hG :
      Real.log ((5 ^ (2 * (g * m)) : ℕ) : ℝ) /
          ((2 * ((l + g) * m) : ℕ) : ℝ) =
        (g : ℝ) / ((l + g : ℕ) : ℝ) * Real.log 5)
    (hL :
      Real.log ((5 ^ (2 * (l * m)) : ℕ) : ℝ) /
          ((2 * ((l + g) * m) : ℕ) : ℝ) =
        (l : ℝ) / ((l + g : ℕ) : ℝ) * Real.log 5) :
    Real.log ((5 ^ (4 * (g * m) + 2 * (l * m)) : ℕ) : ℝ) /
        ((2 * ((l + g) * m) : ℕ) : ℝ) =
      ((2 * g + l : ℕ) : ℝ) / ((l + g : ℕ) : ℝ) * Real.log 5 := by
  calc
    Real.log ((5 ^ (4 * (g * m) + 2 * (l * m)) : ℕ) : ℝ) /
          ((2 * ((l + g) * m) : ℕ) : ℝ) =
        2 * (Real.log ((5 ^ (2 * (g * m)) : ℕ) : ℝ) /
          ((2 * ((l + g) * m) : ℕ) : ℝ)) +
        Real.log ((5 ^ (2 * (l * m)) : ℕ) : ℝ) /
          ((2 * ((l + g) * m) : ℕ) : ℝ) := by
      simp only [Nat.cast_pow, Real.log_pow]
      push_cast
      ring
    _ = 2 * ((g : ℝ) / ((l + g : ℕ) : ℝ) * Real.log 5) +
        (l : ℝ) / ((l + g : ℕ) : ℝ) * Real.log 5 := by rw [hG, hL]
    _ = ((2 * g + l : ℕ) : ℝ) / ((l + g : ℕ) : ℝ) * Real.log 5 := by
      push_cast
      ring

/-!
## Cyclic orientations

For the literal `121` and `211` sources the prescribed Z mode is one of the
two uniform directional modes of the original `112` profile.  The star family
itself is cyclically permuted, so we first extract from its unpermuted
`CTensorOneHOneCertificate`s and then use cyclic invariance of full
six-symmetrization.  This avoids asserting the false statement that a cyclic
permutation of a `C`-tensor is again a `C`-tensor over the same distinguished
mode.
-/

private noncomputable def bareStarFamilyCertificate
    {K : Type u} [Field K]
    (N L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (hcertificate : ∀ a : Fin A,
      (∀ sigma : Fin 3 → Fin (H + 1),
        sigma ∉ Finset.univ.image (cTensorOneHOneAddress H) →
          (starGrading (grading K 5) family a).blockTensor sigma = 0) ∧
      ∀ h : Fin H,
        TensorObj.Isomorphic
          (MMObj K (5 ^ (2 * G)) (5 ^ (2 * L)) (5 ^ (2 * G)))
          ((starGrading (grading K 5) family a).blockSubtensor
            (cTensorOneHOneAddress H h))) :
    CTensorOneHOneFamilyCertificate
      (TensorObj.bigAdd (starObj (grading K 5) family))
      A H (5 ^ (4 * G + 2 * L)) where
  star := starObj (grading K 5) family
  restrict := by
    refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    rw [PiTensorProduct.map_id, LinearMap.id_coe, id_eq]
  certificate a := {
    grading := starGrading (grading K 5) family a
    supported := (hcertificate a).1
    m := fun _ ↦ 5 ^ (2 * G)
    n := fun _ ↦ 5 ^ (2 * L)
    p := fun _ ↦ 5 ^ (2 * G)
    component := (hcertificate a).2
    common_volume := by
      intro h
      rw [← pow_add, ← pow_add]
      congr 1
      omega }

private theorem rotatedExactPower_six_finite_rate_of_capacity
    {K : Type u} [Field K]
    (l g m A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      ((l + g) * m) (l * m) (g * m) A H)
    (e : Equiv.Perm (Fin 3))
    (he : e = cyclicPerm ∨ e = cyclicPerm.trans cyclicPerm)
    (beta : Fin 3 → Profile 2)
    (hbeta : ∀ mode sigma,
      (beta mode).probability sigma =
        (profileProbability
          ((l : ℚ) / (2 * ((l + g : ℕ) : ℚ))) mode sigma : ℝ))
    (hcertificate : ∀ a : Fin A,
      (∀ sigma : Fin 3 → Fin (H + 1),
        sigma ∉ Finset.univ.image (cTensorOneHOneAddress H) →
          (starGrading (grading K 5) family a).blockTensor sigma = 0) ∧
      ∀ h : Fin H,
        TensorObj.Isomorphic
          (MMObj K (5 ^ (2 * (g * m))) (5 ^ (2 * (l * m)))
            (5 ^ (2 * (g * m))))
          ((starGrading (grading K 5) family a).blockSubtensor
            (cTensorOneHOneAddress H h)))
    (hrotated : TensorObj.Restrict
      (TensorObj.permObj e
        (TensorObj.bigAdd (starObj (grading K 5) family)))
      (MME.CompleteSplitCanonicalSquare.restrictedPower K 5
        (fun i ↦ cwSquareBlockType 1 1 2 (e.symm i))
        (fun i ↦ beta (e.symm i)) 0
        (2 * ((l + g) * m))))
    (tau C R : ℝ) (hR : 0 ≤ R) (hH : 0 < H)
    (hHbound : H ≤ 4 ^ ((l + g) * m))
    (hrate :
      R ^ (2 * ((l + g) * m)) *
          Real.exp (-C * Real.sqrt
            (((((l + g) * m) + 1 : ℕ) : ℝ))) ≤
        (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
          ((((5 ^ (4 * (g * m) + 2 * (l * m))) ^ 3 : ℕ) : ℝ) ^ tau)) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization
          (MME.CompleteSplitCanonicalSquare.restrictedPower K 5
            (fun i ↦ cwSquareBlockType 1 1 2 (e.symm i))
            (fun i ↦ beta (e.symm i)) 0 (2 * ((l + g) * m)))) ∧
      R ^ (4 * ((l + g) * m)) *
          Real.exp (-(2 * C + 400) * Real.sqrt
            (((((l + g) * m) + 1 : ℕ) : ℝ))) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  let stars := bareStarFamilyCertificate
    ((l + g) * m) (l * m) (g * m) A H family hcertificate
  rcases mme_Ctensor_one_half_family_to_six_finite_rate_of_capacity
      (K := K) tau C R ((l + g) * m) A H
      (5 ^ (4 * (g * m) + 2 * (l * m))) stars
      hR hH hHbound hrate with
    ⟨q, a, b, c, hrestrict, hweight⟩
  let sourceStars : TensorObj K 3 :=
    TensorObj.bigAdd (starObj (grading K 5) family)
  change TensorObj.Restrict
    (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
    (sixSymmetrization sourceStars) at hrestrict
  change TensorObj.Restrict
    (TensorObj.permObj e sourceStars)
    (MME.CompleteSplitCanonicalSquare.restrictedPower K 5
      (fun i ↦ cwSquareBlockType 1 1 2 (e.symm i))
      (fun i ↦ beta (e.symm i)) 0 (2 * ((l + g) * m))) at hrotated
  have hcyclic : TensorObj.Isomorphic
      (sixSymmetrization (TensorObj.permObj e sourceStars))
      (sixSymmetrization sourceStars) := by
    rcases he with rfl | rfl
    · exact (mme_sixSymmetrization_isomorphic_cyclic_orbit sourceStars).1
    · exact (mme_sixSymmetrization_isomorphic_cyclic_orbit sourceStars).2
  refine ⟨q, a, b, c, ?_, hweight⟩
  have h₁ : TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
      (sixSymmetrization (TensorObj.permObj e sourceStars)) :=
    restrict_trans hrestrict hcyclic.2
  exact restrict_trans h₁ (mme_sixSymmetrization_restrict hrotated)

/-- The exact prescribed-Z six-value endpoint for either literal cyclic
orientation of the canonical square coupled block.  Its Z profile is the
uniform directional split `[l+g,l+g,0]/(2(l+g))`; the entropy and matrix
volume rates still come from the original `112` parameter `l/(2(l+g))`. -/
theorem solution
    {K : Type u} [Field K]
    (l g : ℕ) (hbalance : 341 * l < 100 * g)
    (e : Equiv.Perm (Fin 3))
    (he : e = cyclicPerm ∨ e = cyclicPerm.trans cyclicPerm)
    (tau : ℝ) :
    ∃ beta : Fin 3 → Profile 2,
      (∀ mode sigma,
        (beta mode).probability sigma =
          (profileProbability
            ((l : ℚ) / (2 * ((l + g : ℕ) : ℚ))) mode sigma : ℝ)) ∧
      let rho : Fin 3 → Fin 5 :=
        fun i ↦ cwSquareBlockType 1 1 2 (e.symm i)
      let rateLog : ℝ :=
        Real.log 2 * mme_modern_entropyBits (beta 2).probability +
          2 * Real.log 2 +
          3 * tau *
            (((2 * g + l : ℕ) : ℝ) / ((l + g : ℕ) : ℝ) * Real.log 5)
      HasSixSequenceRate TensorObj.Restrict
        (fun m ↦ MME.CompleteSplitCanonicalSquare.restrictedPower K 5 rho
          (fun i ↦ beta (e.symm i)) 0 (2 * ((l + g) * m)))
        (fun m ↦ 2 * ((l + g) * m)) tau
        (Real.exp (rateLog / 3)) := by
  rcases mme_complete_split_112_cyclic_canonical_directional_rates.{u}
      l g hbalance with ⟨beta, hbeta, hfamilies⟩
  refine ⟨beta, hbeta, ?_⟩
  dsimp only
  let E : ℝ := Real.log 2 * mme_modern_entropyBits (beta 2).probability
  let S : ℝ :=
    ((2 * g + l : ℕ) : ℝ) / ((l + g : ℕ) : ℝ) * Real.log 5
  let rateLog : ℝ := E + 2 * Real.log 2 + 3 * tau * S
  change HasSixSequenceRate TensorObj.Restrict
    (fun m ↦ MME.CompleteSplitCanonicalSquare.restrictedPower K 5
      (fun i ↦ cwSquareBlockType 1 1 2 (e.symm i))
      (fun i ↦ beta (e.symm i)) 0 (2 * ((l + g) * m)))
    (fun m ↦ 2 * ((l + g) * m)) tau
    (Real.exp (rateLog / 3))
  rw [HasSixSequenceRate]
  refine ⟨(Real.exp_pos _).le, ?_⟩
  intro W hW hWrate cutoff
  have hlogW : Real.log W < rateLog / 3 := by
    apply Real.exp_lt_exp.mp
    simpa only [Real.exp_log hW] using hWrate
  let gap : ℝ := rateLog - 3 * Real.log W
  have hgap : 0 < gap := by
    dsimp only [gap]
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let delta : ℝ := min (gap / 6) (Real.log 2 / 2)
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min (div_pos hgap (by norm_num))
      (div_pos hlog2 (by norm_num))
  have hdeltaGap : 6 * delta ≤ gap := by
    have hmin := min_le_left (gap / 6) (Real.log 2 / 2)
    dsimp only [delta]
    nlinarith
  have hdeltaLog : delta < Real.log 2 := by
    have hmin := min_le_right (gap / 6) (Real.log 2 / 2)
    dsimp only [delta]
    linarith
  have hevFamily := hfamilies delta hdelta
  have hlg : 0 < l + g := by omega
  have hevSqrt := sqrt_loss_absorption (l + g) hlg gap hgap
  have hevCut : ∀ᶠ m : ℕ in atTop, max cutoff 1 ≤ m :=
    eventually_ge_atTop (max cutoff 1)
  rcases ((hevFamily.and hevSqrt).and hevCut).exists with
    ⟨m, ⟨hmFamily, hmSqrt⟩, hmCut⟩
  dsimp only at hmFamily
  rcases hmFamily with
    ⟨A, H, family, hA, hHbound, hlogA, hlogAH, hG, hL, hsource⟩
  have hsourceK := hsource K 0
  have hcertificate := hsourceK.1.2
  have hrotated := (hsourceK.2 e he).1
  have hm1 : 1 ≤ m := le_trans (le_max_right cutoff 1) hmCut
  have hm : 0 < m := Nat.zero_lt_of_lt hm1
  have hN : 0 < (l + g) * m := Nat.mul_pos hlg hm
  have hH : 0 < H := by
    by_contra hnot
    have hHzero : H = 0 := Nat.eq_zero_of_not_pos hnot
    subst H
    norm_num at hlogAH
    have hdiff : 0 < Real.log 2 - delta := sub_pos.mpr hdeltaLog
    have hlgR : 0 < (l : ℝ) + (g : ℝ) := by exact_mod_cast hlg
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have hleft :
        0 < 2 * (((l : ℝ) + (g : ℝ)) * (m : ℝ)) *
          (Real.log 2 - delta) :=
      mul_pos (mul_pos (by positivity) (mul_pos hlgR hmR)) hdiff
    exact (not_lt_of_ge hlogAH) hleft
  have hvolumeLog :
      Real.log ((5 ^ (4 * (g * m) + 2 * (l * m)) : ℕ) : ℝ) /
          ((2 * ((l + g) * m) : ℕ) : ℝ) = S := by
    dsimp only [S]
    exact square112_volume_log_rate l g m hlg hm hG hL
  have hrate :
      Real.exp (rateLog - 3 * delta) ^ (2 * ((l + g) * m)) ≤
        (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
          ((((5 ^ (4 * (g * m) + 2 * (l * m))) ^ 3 : ℕ) : ℝ) ^ tau) := by
    dsimp only [rateLog]
    exact capacity_from_log_rates
      ((l + g) * m) A H (5 ^ (4 * (g * m) + 2 * (l * m)))
      tau E S delta hN hA hH hlogA hlogAH hvolumeLog (by positivity)
  rcases rotatedExactPower_six_finite_rate_of_capacity (K := K)
      l g m A H family e he beta hbeta
      hcertificate hrotated tau 0 (Real.exp (rateLog - 3 * delta))
      (Real.exp_pos _).le hH hHbound (by simpa using hrate) with
    ⟨q, a, b, c, hrestrict, hweight⟩
  have hweight' :
      Real.exp (rateLog - 3 * delta) ^ (4 * ((l + g) * m)) *
          Real.exp (-400 * Real.sqrt
            (((((l + g) * m) + 1 : ℕ) : ℝ))) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
    simpa only [mul_zero, zero_add, neg_mul] using hweight
  have habsorb :
      W ^ (12 * ((l + g) * m)) ≤
        Real.exp (rateLog - 3 * delta) ^ (4 * ((l + g) * m)) *
          Real.exp (-400 * Real.sqrt
            (((((l + g) * m) + 1 : ℕ) : ℝ))) := by
    apply strict_base_absorb W rateLog hW ((l + g) * m) delta
    · simpa only [gap] using hdeltaGap
    · simpa only [gap] using hmSqrt
  have htotal := habsorb.trans hweight'
  have hmCutoff : cutoff ≤ m := le_trans (le_max_left cutoff 1) hmCut
  have hfactor : 1 ≤ 2 * (l + g) := by omega
  have hmLength : cutoff ≤ 2 * ((l + g) * m) := by
    calc
      cutoff ≤ m := hmCutoff
      _ ≤ (2 * (l + g)) * m := by
        simpa [one_mul] using Nat.mul_le_mul_right m hfactor
      _ = 2 * ((l + g) * m) := by ring
  refine ⟨m, hmCutoff, hmLength, q, a, b, c, hrestrict, ?_⟩
  convert htotal using 1 <;> ring


