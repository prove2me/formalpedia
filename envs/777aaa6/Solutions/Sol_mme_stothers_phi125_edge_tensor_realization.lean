-- Prove2me | solution 1 for mme_stothers_phi125_edge_tensor_realization
-- status  : ACCEPTED   (disprove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T12:56:29.81472+00:00
-- url     : https://prove2.me/submissions/d5f84b98-2f2f-4a67-a397-b0a3efa6221b

import Definitions.Def_mme_duality
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi125_profile_data
import Definitions.Def_mme_tau_value
import Definitions.Def_mme_tensor_bridge
import Definitions.Def_mme_tensor_quotient
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Defs

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

/- Reused with attribution: marwahaha, Prove2Me accepted submission 909502aa-5cb3-420b-9051-f73954bbee54. The exported solution is renamed to its published theorem name. -/
section Imported_mme_restrict_kronPow

open MME

universe u


theorem mme_restrict_kronPow
    {K : Type u} [Field K] {X Y : TensorObj K 3}
    (h : TensorObj.Restrict X Y) (N : ℕ) :
    TensorObj.Restrict (X.kronPow N) (Y.kronPow N) := by
  induction N with
  | zero => exact TensorObj.Restrict.refl _
  | succ N ih =>
      change TensorObj.Restrict
        (TensorObj.kron X (X.kronPow N))
        (TensorObj.kron Y (Y.kronPow N))
      let P := TensorQ.tensorStrassen K 3 (by norm_num)
      have hx : P.le (TensorQ.toQ X) (TensorQ.toQ Y) := h
      have hp : P.le (TensorQ.toQ (X.kronPow N))
          (TensorQ.toQ (Y.kronPow N)) := ih
      have hleft := P.mul_right _ _ hx (TensorQ.toQ (X.kronPow N))
      have hright := P.mul_right _ _ hp (TensorQ.toQ Y)
      have hmul : P.le
          (TensorQ.toQ X * TensorQ.toQ (X.kronPow N))
          (TensorQ.toQ Y * TensorQ.toQ (Y.kronPow N)) := by
        exact P.le_trans _ _ _ hleft (by simpa [mul_comm] using hright)
      exact hmul


end Imported_mme_restrict_kronPow

/- Reused with attribution: marwahaha, Prove2Me accepted submission 33356640-ad4e-478a-98dc-ca2de641e39b. The exported solution is renamed to its published theorem name. -/
section Imported_mme_HasTauValueAtLeast_mono_restrict

open MME BigOperators Filter

universe u

theorem mme_HasTauValueAtLeast_mono_restrict
    {K : Type u} [Field K]
    {X Y : TensorObj K 3} {tau V : ℝ}
    (hXY : TensorObj.Restrict X Y)
    (hX : HasTauValueAtLeast X tau V) :
    HasTauValueAtLeast Y tau V := by
  refine ⟨hX.1, ?_⟩
  intro epsilon hepsilon
  exact (hX.2 epsilon hepsilon).mono (fun N hN => by
    obtain ⟨k, a, b, c, hrestrict, hweight⟩ := hN
    refine ⟨k, a, b, c, ?_, hweight⟩
    exact TensorObj.Restrict.trans hrestrict
      (mme_restrict_kronPow hXY N))

end Imported_mme_HasTauValueAtLeast_mono_restrict

/- Reused with attribution: marwahaha, Prove2Me accepted submission 2796b1f5-3b44-4d99-bb55-7f7f25865b06. The exported solution is renamed to its published theorem name. -/
section Imported_mme_asymptotic_sum_inequality_sharp

open MME BigOperators

universe u

namespace MME

private theorem MMData.sum_inequality_sharp
    {R : Type u} [CommSemiring R] (P : StrassenPreorder R)
    (D : MMData R P) {iota : Type*} [Fintype iota]
    (n m p : iota → ℕ)
    (hn : ∀ i, 1 ≤ n i) (hm : ∀ i, 1 ≤ m i) (hp : ∀ i, 1 ≤ p i) :
    ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ (D.omegaAbs / 3) ≤
      StrassenPreorder.asymptoticRank P
        (∑ i, D.MMel (n i) (m i) (p i)) := by
  let rankBound := StrassenPreorder.asymptoticRank P
    (∑ i, D.MMel (n i) (m i) (p i))
  have hspec : ∀ phi : AsymptoticSpectrumPoint R P,
      ∑ i, phi (D.MMel (n i) (m i) (p i)) ≤ rankBound := by
    intro phi
    have h_le_AR := StrassenPreorder.eval_le_asymptoticRank P
      (∑ i, D.MMel (n i) (m i) (p i)) phi
    rwa [map_sum] at h_le_AR
  have htheta : ∀ phi : AsymptoticSpectrumPoint R P,
      ∑ i, (n i : ℝ) ^ D.θ₁ phi * (m i : ℝ) ^ D.θ₂ phi *
        (p i : ℝ) ^ D.θ₃ phi ≤ rankBound := by
    intro phi
    rw [show (∑ i, (n i : ℝ) ^ D.θ₁ phi * (m i : ℝ) ^ D.θ₂ phi *
          (p i : ℝ) ^ D.θ₃ phi) =
        ∑ i, phi (D.MMel (n i) (m i) (p i)) from
      Finset.sum_congr rfl fun i _ =>
        (D.MM_eval phi (hn i) (hm i) (hp i)).symm]
    exact hspec phi
  have hn_pos : ∀ i, (0 : ℝ) < (n i : ℝ) := fun i => by
    exact_mod_cast (Nat.zero_lt_of_lt (hn i))
  have hm_pos : ∀ i, (0 : ℝ) < (m i : ℝ) := fun i => by
    exact_mod_cast (Nat.zero_lt_of_lt (hm i))
  have hp_pos : ∀ i, (0 : ℝ) < (p i : ℝ) := fun i => by
    exact_mod_cast (Nat.zero_lt_of_lt (hp i))
  set F : ℝ × ℝ × ℝ → ℝ :=
    fun v => ∑ i, (n i : ℝ) ^ v.1 * (m i : ℝ) ^ v.2.1 *
      (p i : ℝ) ^ v.2.2 with hF
  have hF_convex : ConvexOn ℝ Set.univ F :=
    sum_rpow_convex (fun i => (n i : ℝ)) (fun i => (m i : ℝ))
      (fun i => (p i : ℝ)) hn_pos hm_pos hp_pos
  have hF_perm : ∀ phi : AsymptoticSpectrumPoint R P,
      ∀ sigma ∈ ({Equiv.refl _, cyclicPerm3, cyclicPerm3 * cyclicPerm3} :
          Set (Equiv.Perm (Fin 3))),
        F (permuteTriple sigma (D.θ₁ phi, D.θ₂ phi, D.θ₃ phi)) ≤
          rankBound := by
    intro phi sigma hsigma
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsigma
    obtain ⟨phi', hphi'⟩ := D.cyclic phi
    obtain ⟨phi'', hphi''⟩ := D.cyclic phi'
    obtain ⟨k1, k2, k3⟩ := D.theta_cyclic hphi'
    obtain ⟨l1, l2, l3⟩ := D.theta_cyclic hphi''
    rcases hsigma with h_id | h_c | h_c2
    · subst h_id
      have h_pt :
          permuteTriple (Equiv.refl _) (D.θ₁ phi, D.θ₂ phi, D.θ₃ phi) =
            (D.θ₁ phi, D.θ₂ phi, D.θ₃ phi) := rfl
      rw [h_pt]
      exact htheta phi
    · subst h_c
      have h_pt :
          permuteTriple cyclicPerm3 (D.θ₁ phi, D.θ₂ phi, D.θ₃ phi) =
            (D.θ₃ phi, D.θ₁ phi, D.θ₂ phi) := rfl
      rw [h_pt]
      have e1 : D.θ₁ phi'' = D.θ₃ phi := by rw [l1, k2]
      have e2 : D.θ₂ phi'' = D.θ₁ phi := by rw [l2, k3]
      have e3 : D.θ₃ phi'' = D.θ₂ phi := by rw [l3, k1]
      have h := htheta phi''
      rw [e1, e2, e3] at h
      exact h
    · subst h_c2
      have h_pt :
          permuteTriple (cyclicPerm3 * cyclicPerm3)
              (D.θ₁ phi, D.θ₂ phi, D.θ₃ phi) =
            (D.θ₂ phi, D.θ₃ phi, D.θ₁ phi) := rfl
      rw [h_pt]
      have e1 : D.θ₁ phi' = D.θ₂ phi := k1
      have e2 : D.θ₂ phi' = D.θ₃ phi := k2
      have e3 : D.θ₃ phi' = D.θ₁ phi := k3
      have h := htheta phi'
      rw [e1, e2, e3] at h
      exact h
  have h_avg : ∀ phi : AsymptoticSpectrumPoint R P,
      F ((D.θ₁ phi + D.θ₂ phi + D.θ₃ phi) / 3,
         (D.θ₁ phi + D.θ₂ phi + D.θ₃ phi) / 3,
         (D.θ₁ phi + D.θ₂ phi + D.θ₃ phi) / 3) ≤
        rankBound := fun phi =>
    jensen_S3_convex hF_convex (D.θ₁ phi, D.θ₂ phi, D.θ₃ phi)
      rankBound (hF_perm phi)
  set S : AsymptoticSpectrumPoint R P → ℝ :=
    fun phi => D.θ₁ phi + D.θ₂ phi + D.θ₃ phi with hS_def
  haveI : Nonempty (AsymptoticSpectrumPoint R P) := mme_spectrum_nonempty P
  have h_compact :
      IsCompact (Set.univ : Set (AsymptoticSpectrumPoint R P)) := isCompact_univ
  obtain ⟨phi_max, -, hmax⟩ :=
    h_compact.exists_isMaxOn Set.univ_nonempty
      D.continuous_θsum.continuousOn
  have h_supS : D.omegaAbs = S phi_max := by
    apply le_antisymm
    · refine ciSup_le ?_
      intro phi
      exact hmax (Set.mem_univ phi)
    · exact le_ciSup (f := S)
        ⟨S phi_max, fun y ⟨phi, hphi⟩ => hphi ▸ hmax (Set.mem_univ phi)⟩ phi_max
  rw [h_supS]
  have h_at_max := h_avg phi_max
  have h_eq : ∀ i, ((n i * m i * p i : ℕ) : ℝ) ^ (S phi_max / 3) =
      (n i : ℝ) ^ (S phi_max / 3) * (m i : ℝ) ^ (S phi_max / 3) *
        (p i : ℝ) ^ (S phi_max / 3) := by
    intro i
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (le_of_lt (hn_pos i)) (le_of_lt (hm_pos i))]
  calc
    ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ (S phi_max / 3) =
        ∑ i, (n i : ℝ) ^ (S phi_max / 3) *
          (m i : ℝ) ^ (S phi_max / 3) *
          (p i : ℝ) ^ (S phi_max / 3) :=
      Finset.sum_congr rfl fun i _ => h_eq i
    _ = F (S phi_max / 3, S phi_max / 3, S phi_max / 3) := rfl
    _ ≤ rankBound := h_at_max

private theorem sum_inequality_sharp_pos
    {K : Type u} [Field K] {k : ℕ}
    (n m p : Fin k → ℕ)
    (hn : ∀ i, 1 ≤ n i) (hm : ∀ i, 1 ≤ m i) (hp : ∀ i, 1 ≤ p i) :
    ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ (matMulExp_strassen K / 3) ≤
      tensorAsymptoticRank
        (TensorObj.bigAdd (fun i => MMObj K (n i) (m i) (p i))) := by
  have h := (mmTensorData K).sum_inequality_sharp
    (tensorPreorder K) n m p hn hm hp
  rw [bridge_omega] at h
  change ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^
      (matMulExp_strassen K / 3) ≤
    StrassenPreorder.asymptoticRank (tensorPreorder K)
      (∑ i, MMq K (n i) (m i) (p i)) at h
  rw [bridge_asymptoticRank] at h
  exact h

theorem asymptotic_sum_inequality_sharp_internal
    {K : Type u} [Field K] {k : ℕ} (n m p : Fin k → ℕ) :
    ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^
        (matMulExp_strassen K / 3) ≤
      tensorAsymptoticRank
        (TensorObj.bigAdd (fun i => MMObj K (n i) (m i) (p i))) := by
  classical
  set S : Finset (Fin k) :=
    Finset.univ.filter (fun i => 1 ≤ n i ∧ 1 ≤ m i ∧ 1 ≤ p i) with hS
  set e : Fin S.card ≃ {x // x ∈ S} := (S.equivFin).symm with he
  have hmemS : ∀ x : {x // x ∈ S},
      1 ≤ n x.1 ∧ 1 ≤ m x.1 ∧ 1 ≤ p x.1 := by
    intro x
    have hx : x.1 ∈ Finset.univ.filter
        (fun i => 1 ≤ n i ∧ 1 ≤ m i ∧ 1 ≤ p i) := hS ▸ x.2
    exact (Finset.mem_filter.mp hx).2
  have hn' : ∀ j : Fin S.card, 1 ≤ n (e j).1 := fun j => (hmemS (e j)).1
  have hm' : ∀ j : Fin S.card, 1 ≤ m (e j).1 := fun j => (hmemS (e j)).2.1
  have hp' : ∀ j : Fin S.card, 1 ≤ p (e j).1 := fun j => (hmemS (e j)).2.2
  have hsum_eq :
      (∑ j : Fin S.card, MMq K (n (e j).1) (m (e j).1) (p (e j).1)) =
        ∑ i, MMq K (n i) (m i) (p i) := by
    rw [show (∑ j : Fin S.card,
          MMq K (n (e j).1) (m (e j).1) (p (e j).1)) =
        ∑ x : {x // x ∈ S}, MMq K (n x.1) (m x.1) (p x.1) from
      Equiv.sum_comp e (fun x => MMq K (n x.1) (m x.1) (p x.1))]
    rw [Finset.sum_coe_sort S (fun i => MMq K (n i) (m i) (p i))]
    refine Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => ?_)
    rw [hS, Finset.mem_filter] at hi
    exact MMq_eq_zero_of_not_pos
      (fun hpos => hi ⟨Finset.mem_univ i, hpos⟩)
  have hAR_eq :
      tensorAsymptoticRank
          (TensorObj.bigAdd (fun j =>
            MMObj K (n (e j).1) (m (e j).1) (p (e j).1))) =
        tensorAsymptoticRank
          (TensorObj.bigAdd (fun i => MMObj K (n i) (m i) (p i))) := by
    rw [← bridge_asymptoticRank
      (fun j => n (e j).1) (fun j => m (e j).1) (fun j => p (e j).1),
      hsum_eq, bridge_asymptoticRank n m p]
  have hpos := sum_inequality_sharp_pos (K := K)
    (fun j => n (e j).1) (fun j => m (e j).1) (fun j => p (e j).1)
    hn' hm' hp'
  have hexp_ne : matMulExp_strassen K / 3 ≠ 0 := by
    have := matMulExp_strassen_pos (K := K)
    positivity
  have hreal_eq :
      (∑ j : Fin S.card,
        ((n (e j).1 * m (e j).1 * p (e j).1 : ℕ) : ℝ) ^
          (matMulExp_strassen K / 3)) =
        ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^
          (matMulExp_strassen K / 3) := by
    rw [show (∑ j : Fin S.card,
          ((n (e j).1 * m (e j).1 * p (e j).1 : ℕ) : ℝ) ^
            (matMulExp_strassen K / 3)) =
        ∑ x : {x // x ∈ S},
          ((n x.1 * m x.1 * p x.1 : ℕ) : ℝ) ^
            (matMulExp_strassen K / 3) from
      Equiv.sum_comp e (fun x =>
        ((n x.1 * m x.1 * p x.1 : ℕ) : ℝ) ^
          (matMulExp_strassen K / 3))]
    rw [Finset.sum_coe_sort S (fun i =>
      ((n i * m i * p i : ℕ) : ℝ) ^ (matMulExp_strassen K / 3))]
    refine Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => ?_)
    rw [hS, Finset.mem_filter] at hi
    have hnp : ¬ (1 ≤ n i ∧ 1 ≤ m i ∧ 1 ≤ p i) :=
      fun hpos => hi ⟨Finset.mem_univ i, hpos⟩
    have hzero : n i * m i * p i = 0 := by
      rcases (by omega : n i = 0 ∨ m i = 0 ∨ p i = 0) with h0 | h0 | h0 <;>
        simp [h0]
    rw [hzero, Nat.cast_zero, Real.zero_rpow hexp_ne]
  rw [← hreal_eq, ← hAR_eq]
  exact hpos

end MME

theorem mme_asymptotic_sum_inequality_sharp
    {K : Type u} [Field K] {k : ℕ} (n m p : Fin k → ℕ) :
    ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^
        (MME.matMulExp_strassen K / 3) ≤
      MME.tensorAsymptoticRank
        (MME.TensorObj.bigAdd (fun i => MME.MMObj K (n i) (m i) (p i))) :=
  MME.asymptotic_sum_inequality_sharp_internal n m p

end Imported_mme_asymptotic_sum_inequality_sharp

/- Reused with attribution: marwahaha, Prove2Me accepted submission 74d8d24c-1885-4a4c-9f4d-df3b08ef7bb5. The exported solution is renamed to its published theorem name. -/
section Imported_mme_tensorAsymptoticRank_mono_restrict

open MME

universe u

theorem mme_tensorAsymptoticRank_mono_restrict
    {K : Type u} [Field K] {X Y : TensorObj K 3}
    (h : TensorObj.Restrict X Y) :
    tensorAsymptoticRank X ≤ tensorAsymptoticRank Y := by
  let hd : (1 : ℕ) < 3 := by norm_num
  let P := TensorQ.tensorStrassen K 3 hd
  rw [TensorQ.tensorAsymptoticRank_eq hd X,
    TensorQ.tensorAsymptoticRank_eq hd Y,
    mme_strassen_duality, mme_strassen_duality]
  apply ciSup_le
  intro phi
  have hXY : P.le (TensorQ.toQ X) (TensorQ.toQ Y) := by
    change TensorQ.le (TensorQ.toQ X) (TensorQ.toQ Y)
    exact h
  exact (phi.monotone' hXY).trans
    (le_ciSup (StrassenPreorder.spectrum_eval_bddAbove P (TensorQ.toQ Y)) phi)

end Imported_mme_tensorAsymptoticRank_mono_restrict

/- Reused with attribution: marwahaha, Prove2Me accepted submission 22e9c159-4fc3-4cec-820b-51f705c73211. The exported solution is renamed to its published theorem name. -/
section Imported_mme_tensorAsymptoticRank_kronPow_eq_of_two_le_of_pos

open MME

universe u


theorem mme_tensorAsymptoticRank_kronPow_eq_of_two_le_of_pos
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    (X : TensorObj K d) (N : ℕ) (hN : 1 ≤ N) :
    tensorAsymptoticRank (X.kronPow N) = tensorAsymptoticRank X ^ N := by
  calc
    tensorAsymptoticRank (X.kronPow N) =
        StrassenPreorder.asymptoticRank (TensorQ.tensorStrassen K d hd)
          (TensorQ.toQ (X.kronPow N)) :=
      TensorQ.tensorAsymptoticRank_eq hd (X.kronPow N)
    _ = StrassenPreorder.asymptoticRank (TensorQ.tensorStrassen K d hd)
          ((TensorQ.toQ X) ^ N) := by rw [TensorQ.toQ_kronPow]
    _ = (StrassenPreorder.asymptoticRank (TensorQ.tensorStrassen K d hd)
          (TensorQ.toQ X)) ^ N :=
      StrassenPreorder.asymptoticRank_pow
        (TensorQ.tensorStrassen K d hd) (TensorQ.toQ X) N hN
    _ = tensorAsymptoticRank X ^ N := by
      rw [TensorQ.tensorAsymptoticRank_eq hd X]

end Imported_mme_tensorAsymptoticRank_kronPow_eq_of_two_le_of_pos

/- Reused with attribution: marwahaha, Prove2Me accepted submission 4b9e344e-78bb-4b93-b2ca-290538b5d017. The exported solution is renamed to its published theorem name. -/
section Imported_mme_le_of_frequently_pow_half_le

open Filter

/-!
An elementary analytic endpoint used by the tau-value/rank bridge.  A
frequently occurring exponential inequality with a fixed positive loss still
forces the base on the left to be no larger than the base on the right.
-/

theorem mme_le_of_frequently_pow_half_le {V R : ℝ}
    (hV : 1 ≤ V) (hR : 0 ≤ R)
    (hfreq : ∃ᶠ N : ℕ in atTop,
      V ^ N * (1 / 2 : ℝ) ≤ R ^ N) :
    V ≤ R := by
  by_contra hnot
  have hVR : R < V := lt_of_not_ge hnot
  have hVpos : 0 < V := lt_of_lt_of_le zero_lt_one hV
  have hratio_nonneg : 0 ≤ R / V := div_nonneg hR hVpos.le
  have hratio_lt_one : R / V < 1 := (div_lt_one hVpos).2 hVR
  have htend : Tendsto (fun N : ℕ => (R / V) ^ N) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nonneg hratio_lt_one
  have hevent : ∀ᶠ N : ℕ in atTop, (R / V) ^ N < (1 / 2 : ℝ) :=
    (tendsto_order.1 htend).2 _ (by norm_num)
  rcases (hfreq.and_eventually hevent).exists with ⟨N, hpow, hsmall⟩
  have hVpow : 0 < V ^ N := pow_pos hVpos N
  have hhalf : (1 / 2 : ℝ) ≤ R ^ N / V ^ N := by
    apply (le_div_iff₀ hVpow).2
    simpa [mul_comm] using hpow
  rw [← div_pow] at hhalf
  exact (not_lt_of_ge hhalf) hsmall

end Imported_mme_le_of_frequently_pow_half_le

/- Reused with attribution: marwahaha, Prove2Me accepted submission 419a191e-a4f4-407f-968a-b057128810bd. The exported solution is renamed to its published theorem name. -/
section Imported_mme_tau_value_le_of_asymptoticRank_le

open MME BigOperators Filter

universe u

private lemma tensorAsymptoticRank_nonneg
    {K : Type u} [Field K] {d : ℕ} (T : TensorObj K d) :
    0 ≤ tensorAsymptoticRank T := by
  unfold tensorAsymptoticRank
  apply le_ciInf
  intro n
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem mme_tau_value_le_of_asymptoticRank_le
    {K : Type u} [Field K] {T : TensorObj K 3} {R V : ℝ}
    (hR_nonneg : 0 ≤ R) (hV_one : 1 ≤ V)
    (hR : tensorAsymptoticRank T ≤ R)
    (hV : HasTauValueAtLeast T (matMulExp_strassen K / 3) V) :
    V ≤ R := by
  apply mme_le_of_frequently_pow_half_le hV_one hR_nonneg
  have hwitness := hV.2 (1 / 2) (by norm_num)
  have hlarge : ∀ᶠ N : ℕ in atTop, 1 ≤ N := eventually_ge_atTop 1
  refine (hwitness.and_eventually hlarge).mono ?_
  rintro N ⟨⟨k, a, b, c, hrestrict, hweight⟩, hN⟩
  have hAR_nonneg : 0 ≤ tensorAsymptoticRank T :=
    tensorAsymptoticRank_nonneg T
  calc
    V ^ N * (1 / 2 : ℝ) = V ^ N * (1 - (1 / 2 : ℝ)) := by ring
    _ ≤ ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^
          (matMulExp_strassen K / 3)) := hweight
    _ ≤ tensorAsymptoticRank
          (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i))) :=
      mme_asymptotic_sum_inequality_sharp a b c
    _ ≤ tensorAsymptoticRank (T.kronPow N) :=
      mme_tensorAsymptoticRank_mono_restrict hrestrict
    _ = tensorAsymptoticRank T ^ N :=
      mme_tensorAsymptoticRank_kronPow_eq_of_two_le_of_pos
        (K := K) (by norm_num) T N hN
    _ ≤ R ^ N := pow_le_pow_left₀ hAR_nonneg hR N

end Imported_mme_tau_value_le_of_asymptoticRank_le


open MME BigOperators Filter
universe u

private theorem singleton_sum_restrict
    {K : Type u} [Field K] {k : ℕ} (F : Fin k → TensorObj K 3)
    (hk : k = 1) (T : TensorObj K 3)
    (h : TensorObj.Restrict (TensorObj.bigAdd F) T) :
    ∃ i : Fin k, TensorObj.Restrict (F i) T := by
  subst k
  exact ⟨0, h⟩

theorem solution : ¬ (∀     {K : Type} [Field K]
    (tau : ℝ) (N alpha beta gamma : ℕ)
    (_hN : 0 < N) (_hprofile : alpha + beta + gamma = N)
    (kept : Finset
      (MME.StothersFourth.Phi125.CyclicExactEdge N alpha beta gamma))
    (B : ℝ) (_hB : 0 ≤ B)
    (_hinjective :
      ∀ i : Fin 3,
        Function.Injective (fun e : kept ↦
          MME.StothersFourth.Phi125.cyclicModeWord e.1 i)),
    ∃ (block : kept → TensorObj K 3),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j : Fin kept.card ↦
          block (kept.equivFin.symm j)))
        ((cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 2 5)).kronPow
            (2 * N)) ∧
      (∀ e : kept, ∀ W : ℝ,
        0 ≤ W → W < B → HasTauValueAtLeast (block e) tau W)) := by
  classical
  intro h
  let K := ℚ
  letI : Field K := inferInstanceAs (Field ℚ)
  let w : MME.StothersFourth.Phi125.ExactProfileWord 1 1 0 0 :=
    ⟨![0, 5], by decide⟩
  let edge : MME.StothersFourth.Phi125.CyclicExactEdge 1 1 0 0 := (w,w,w)
  let kept : Finset (MME.StothersFourth.Phi125.CyclicExactEdge 1 1 0 0) := {edge}
  let T : TensorObj K 3 := (cyclicSymmetrization
    (MME.StothersFourth.cwFourthConstituent K 6 1 2 5)).kronPow 2
  let R : ℝ := max 1 (tensorAsymptoticRank T)
  have hR : 1 ≤ R := le_max_left _ _
  have hinj : ∀ i : Fin 3, Function.Injective (fun e : kept ↦
      MME.StothersFourth.Phi125.cyclicModeWord e.1 i) := by
    intro i a b _
    apply Subtype.ext
    have ha : a.1 = edge := Finset.mem_singleton.mp a.2
    have hb : b.1 = edge := Finset.mem_singleton.mp b.2
    exact ha.trans hb.symm
  obtain ⟨block, hres, hval⟩ := h (K := K) (matMulExp_strassen K / 3)
    1 1 0 0 (by norm_num) (by norm_num) kept (R+2) (by linarith) hinj
  obtain ⟨i, hi⟩ := singleton_sum_restrict
    (fun j : Fin kept.card => block (kept.equivFin.symm j))
    (by simp [kept]) T hres
  have hv := hval (kept.equivFin.symm i) (R+1) (by linarith) (by linarith)
  have ht := mme_HasTauValueAtLeast_mono_restrict hi hv
  have hle := mme_tau_value_le_of_asymptoticRank_le
    (T := T) (R := R) (V := R+1) (by linarith) (by linarith)
    (le_max_right _ _) ht
  linarith
