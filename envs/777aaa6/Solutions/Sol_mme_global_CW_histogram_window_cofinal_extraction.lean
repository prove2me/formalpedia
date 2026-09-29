-- Prove2me | solution 1 for mme_global_CW_histogram_window_cofinal_extraction
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T10:29:58.61277+00:00
-- url     : https://prove2.me/submissions/276b4570-16d4-400f-9deb-6c80545397c1

import Definitions.Def_mme_global_CW_entropy_data
import Definitions.Def_mme_global_CW_histogram_frame
import Definitions.Def_mme_global_CW_joint_start_data
import Theorems.Thm_mme_global_CW_histogram_window_stage_family
import Theorems.Thm_mme_global_CW_canonical_cofinal_entropy_bound
import Theorems.Thm_mme_global_CW_counted_profile_family_extraction
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.RegionRate MME.RecursiveYZ MME.GlobalCW
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2000000
universe u

private theorem type_log_bound {C d k L t a : ℕ} (hk : 1 ≤ k) (ht : 1 ≤ t)
    (hL : L ≤ C*k^2) (ha : a ≤ d) (htypes : t ≤ (L+1)^a) :
    Real.log (t : ℝ) ≤ ((d : ℝ)*Real.log ((C : ℝ)+1) + 2*d) * k := by
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hLreal : (L : ℝ) ≤ (C : ℝ)*(k : ℝ)^2 := by exact_mod_cast hL
  have hbase : (L : ℝ)+1 ≤ ((C : ℝ)+1)*((k : ℝ)+1)^2 := by
    have hC : (0 : ℝ) ≤ C := by positivity
    have hk0 : (0 : ℝ) ≤ k := by positivity
    nlinarith [mul_nonneg hC hk0]
  have hpoly : (t : ℝ) ≤ (((C : ℝ)+1)*((k : ℝ)+1)^2)^d := by
    have ht' : (t : ℝ) ≤ ((L : ℝ)+1)^a := by exact_mod_cast htypes
    apply ht'.trans
    apply (pow_le_pow_left₀ (by positivity) hbase a).trans
    apply pow_le_pow_right₀ _ ha
    have hC : 1 ≤ (C : ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) C; linarith
    exact one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (by linarith))
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht)
  have hlog := Real.log_le_log ht0 hpoly
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
  have hlogk : Real.log ((k : ℝ)+1) ≤ k := by
    simpa using Real.log_le_sub_one_of_pos (show 0 < (k : ℝ)+1 by positivity)
  have hlogC : 0 ≤ Real.log ((C : ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) C; linarith)
  norm_num only [Nat.cast_ofNat] at hlog
  have hd : (0 : ℝ) ≤ d := by positivity
  nlinarith [mul_nonneg hd (sub_nonneg.mpr hlogk),
    mul_nonneg (mul_nonneg hd hlogC) (sub_nonneg.mpr hkreal)]

theorem solution {K : Type u} [Field K] (C H d : ℕ) (B E rho : ℝ)
    (hB : 0 ≤ B) (hrho : 0 ≤ rho) (hgap : rho < E) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∃ hk : 1 < k,
      ∀ {ell M : ℕ} (D : HistogramFrame ell M)
        (good : Fin 3 → (Cell D.degree D.R D.bounds → CompleteSplit.CompleteWord ell → ℕ) → Prop),
      (∃ x : Fin 3 → FineWord M, supported x ∧ ∀ i, D.window good i (x i)) →
      M ≤ C*k^2 → D.degree ≤ H →
      Fintype.card (Cell D.degree D.R D.bounds) ≤ d →
      D.R*(D.degree+1) ≤ d →
      D.R*(D.degree+1)*Fintype.card (CompleteSplit.CompleteWord ell) ≤ d →
      3*Fintype.card (Cell D.degree D.R D.bounds)*Fintype.card (CompleteSplit.CompleteWord ell) ≤ d →
      (∀ mu : D.AdmissibleProfile, (∀ i, good i (mu.val i)) →
        E*(k : ℝ)^2 ≤ (D.stage mu k hk).entropyRate) →
      (∀ mu : D.AdmissibleProfile, (∀ i, good i (mu.val i)) →
        (D.stage mu k hk).entropyExponent ≤ B*(k : ℝ)^2) →
      ∃ S : GlobalCW.Part M ell (D.window good),
        1 ≤ S.inputs ∧
        S.inputs ≤ (D.L+1)^(3*Fintype.card (Cell D.degree D.R D.bounds)*
          Fintype.card (CompleteSplit.CompleteWord ell)) ∧
        rho*(k : ℝ)^2 + Real.log (S.inputs : ℝ) ≤ S.rate ∧
        Restrict (bigAdd (fun _ : Fin ⌈Real.exp S.rate⌉₊ ↦ tensor K (D.window good)))
          (bigAdd (fun _ : Fin S.inputs ↦ tensor K (fun _ (_ : FineWord M) ↦ True))) := by
  let middle : ℝ := (E+rho)/2
  have hmid : rho < middle ∧ middle < E := by dsimp [middle]; constructor <;> linarith
  let delta : ℝ := middle-rho
  have hdelta : 0 < delta := sub_pos.mpr hmid.1
  let loss : ℝ := (d : ℝ)*Real.log ((C : ℝ)+1) + 2*d
  obtain ⟨kC,hkC⟩ := mme_global_CW_canonical_cofinal_entropy_bound C H d B E middle hB hmid.2
  obtain ⟨kT,hkT⟩ := exists_nat_gt (loss/delta)
  refine ⟨max kC kT,?_⟩
  intro k hk
  obtain ⟨hk1,hcount⟩ := hkC k ((le_max_left _ _).trans hk)
  refine ⟨hk1,?_⟩
  intro ell M D good hne hsize hdegree hc hj hw ht hE htheta
  obtain ⟨types,profiles,hpoly,hgood,inside,cover⟩ :=
    mme_global_CW_histogram_window_stage_family D good k hk1
  have htypes : 1 ≤ types := by
    obtain ⟨x,hs,hx⟩ := hne
    obtain ⟨j,hj,_⟩ := cover x hs hx
    have := j.isLt
    omega
  have hL : D.L ≤ C*k^2 :=
    ((Nat.le_mul_of_pos_right D.L (show 0 < 2^(ell-1) by positivity)).trans_eq D.length).trans hsize
  have hlog := type_log_bound (Nat.le_of_lt hk1) htypes hL ht hpoly
  have hkT' : (kT : ℝ) ≤ k := by exact_mod_cast (le_max_right kC kT).trans hk
  have hloss : loss ≤ delta*(k : ℝ) := by
    have hh : loss/delta ≤ (k : ℝ) := (hkT.trans_le hkT').le
    simpa only [mul_comm] using (div_le_iff₀ hdelta).mp hh
  have hrate : 0 ≤ middle*(k : ℝ)^2 := mul_nonneg (hrho.trans hmid.1.le) (sq_nonneg _)
  obtain ⟨S,hinputs,hrate_eq,hrestriction⟩ :=
    mme_global_CW_counted_profile_family_extraction (K := K) (D.window good)
      (fun j ↦ D.stage (profiles j) k hk1) (middle*(k : ℝ)^2) hrate
      (fun j ↦ hcount D (profiles j) hsize hdegree hc hj hw
        (hE (profiles j) (hgood j)) (htheta (profiles j) (hgood j))) inside cover
  refine ⟨S,?_,?_,?_,?_⟩
  · simpa only [hinputs] using htypes
  · simpa only [hinputs] using hpoly
  · rw [hinputs,hrate_eq]
    have hh := mul_le_mul_of_nonneg_right hloss (show (0 : ℝ) ≤ k by positivity)
    dsimp [loss] at hloss
    dsimp [delta] at hh
    nlinarith
  · rw [hrate_eq,hinputs]
    exact hrestriction
