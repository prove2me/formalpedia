-- Prove2me | solution 1 for dlp_pair_perfiber_sigma_survival_mixed
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T21:53:09.466547+00:00
-- url     : https://prove2.me/submissions/2b68ec34-58a2-4996-83bc-735aff4f911d

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_rademacher
import Definitions.Def_matrix_completion_bernoulli
import Theorems.Thm_spectral_norm_dual_attainment
import Theorems.Thm_spectral_norm_inner_pairing_bound
import Theorems.Thm_rademacher_expectation_eq_bernoulli_half_expectation
import Theorems.Thm_bernoulli_powerset_expectation_double
import Theorems.Thm_bernoulli_powerset_expectation_pair_coordinate
import Theorems.Thm_bernoulli_powerset_expectation_single_coordinate
import Theorems.Thm_bernoulli_powerset_expectation_linear
import Theorems.Thm_dlp_conditional_lemma2_sigma_fiber_mixed_chaos_inl
import Mathlib.Analysis.InnerProductSpace.Basic
open MatrixCompletion
open scoped BigOperators Classical InnerProductSpace

/-
de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211) §4 eq (6): the TOTAL
hypothesis-free per-fiber σ-survival lower bound on the concrete matrix MIXED
(linear + bilinear, degree-≤2) chaos.

This is the MIXED analog of `dlp_pair_perfiber_sigma_survival_offdiag` (8eb5e7a1).
The dlP forward bound applies Lemma 2 (eq 6) with the mean-zero σ-fluctuation
`ξ_σ = 4·decoupled(Z_σ) − T_{n,2}`, which carries a generically-nonzero LINEAR (r=1)
term `Σ_w ε_w • b w` IN ADDITION to the bilinear (r=2) term — exactly dlP Lemma 2's
degree-≤k tetrahedral chaos `Σ_{r=1}^k`. The pure-bilinear child 8eb5e7a1 only closes
the b=0 case; this node covers b≠0.

Composes the Proved pieces:
  • norming-pair existence (06fa187a, spectral_norm_dual_attainment);
  • mean-0 of the σ-chaos dual image: LINEAR term via single-coordinate marginal
    (740c5573, g(x)=2x−1 ⇒ ½·1+½·(−1)=0), BILINEAR term via pair-coordinate
    marginal (e1573ddf), σ-fiber bridge a2fb59eb + double linearity 726fbda4;
  • CASE SPLIT on E_σ[F²]:
      – 0 < E_σ[F²]  → dlp_conditional_lemma2_sigma_fiber_mixed_chaos_inl (mixed cond Lemma 2);
      – E_σ[F²] = 0  → inline degenerate branch (pairing splits linearly,
        ⟪(T+Ξ)xv,yv⟫=spectralNorm T+0 ≤ spectralNorm(T+Ξ), survival ≡ 1).
Source: dlP–MS 1995, §4, eq (6) p.5 (/tmp/dlp.txt lines 199–235, 518–527) + Lemma 2.
-/

namespace MixedPerFiberSurvival

/-- The MIXED matrix-valued σ-sign chaos
`Ξ(ε) = ∑_w (ε_w) • b w + ∑_{w₁ ≠ w₂} (ε_{w₁} ε_{w₂}) • a w₁ w₂`. -/
noncomputable def mchaos {n1 n2 : Nat}
    (b : (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (eps : Finset (Fin n1 × Fin n2)) : RealMatrix n1 n2 :=
  (∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • b w)
  + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
      (if w1 = w2 then (0 : RealMatrix n1 n2)
       else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2))

end MixedPerFiberSurvival

open MixedPerFiberSurvival

theorem solution
    {n1 n2 : Nat}
    (b : (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (T : RealMatrix n1 n2) :
    rademacherExpectation
        (fun eps =>
          if spectralNorm T ≤ spectralNorm (T +
            ((∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • b w)
              + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
                (if w1 = w2 then (0 : RealMatrix n1 n2)
                 else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2))))
          then (1 : ℝ) else 0) ≥ 1 / 324 := by
  classical
  obtain ⟨xv, yv, hxv, hyv, hnorm⟩ := spectral_norm_dual_attainment T
  -- scalar dual image of the MIXED σ-chaos
  set F : Finset (Fin n1 × Fin n2) → ℝ :=
    fun eps => ⟪Matrix.toEuclideanLin (mchaos b a eps) xv, yv⟫_ℝ with hF
  set bc : (Fin n1 × Fin n2) → ℝ :=
    fun w => ⟪Matrix.toEuclideanLin (b w) xv, yv⟫_ℝ with hbc
  set ac : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → ℝ :=
    fun w1 w2 => ⟪Matrix.toEuclideanLin (a w1 w2) xv, yv⟫_ℝ with hac
  -- F is the off-diagonal scalar MIXED sign-chaos with coefficients (bc, ac)
  have hFchaos :
      ∀ eps,
        F eps =
          (∑ w : Fin n1 × Fin n2, bc w * rademacherSign eps w.1 w.2)
            + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
                (if w1 = w2 then (0 : ℝ)
                 else ac w1 w2 * rademacherSign eps w1.1 w1.2
                              * rademacherSign eps w2.1 w2.2)) := by
    intro eps
    simp only [hF, mchaos]
    rw [map_add, LinearMap.add_apply, inner_add_left]
    congr 1
    · rw [map_sum, LinearMap.sum_apply, sum_inner]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [map_smul, LinearMap.smul_apply, inner_smul_left]
      simp only [hbc, conj_trivial]; ring
    · rw [map_sum, LinearMap.sum_apply, sum_inner]
      refine Finset.sum_congr rfl (fun w1 _ => ?_)
      rw [map_sum, LinearMap.sum_apply, sum_inner]
      refine Finset.sum_congr rfl (fun w2 _ => ?_)
      by_cases h : w1 = w2
      · simp [h]
      · simp only [if_neg h]
        rw [map_smul, LinearMap.smul_apply, inner_smul_left]
        simp only [hac, conj_trivial]; ring
  -- MEAN-0: linear half + bilinear half both vanish under σ.
  have hmean : rademacherExpectation F = 0 := by
    -- write F as a single double-sum-ish indicator function, split into lin + bil
    -- represent F in indicator form
    set L : Finset (Fin n1 × Fin n2) → ℝ :=
      fun eps => ∑ w : Fin n1 × Fin n2, bc w * rademacherSign eps w.1 w.2 with hL
    set Bl : Finset (Fin n1 × Fin n2) → ℝ :=
      fun eps => ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
        (if w1 = w2 then (0 : ℝ)
         else ac w1 w2 * rademacherSign eps w1.1 w1.2
                      * rademacherSign eps w2.1 w2.2) with hBl
    have hFsplit : F = (fun eps => L eps + Bl eps) := by funext eps; rw [hFchaos eps]
    have hLBmean : rademacherExpectation (fun eps => L eps + Bl eps) = 0 := by
      -- additivity of rademacherExpectation
      have hadd : rademacherExpectation (fun eps => L eps + Bl eps)
          = rademacherExpectation L + rademacherExpectation Bl := by
        unfold rademacherExpectation
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro eps _; ring
      rw [hadd]
      -- LINEAR half = 0
      have hLmean : rademacherExpectation L = 0 := by
        -- indicator form: rademacherSign = 2·(ind) − 1
        have hLind : L = (fun eps =>
            ∑ w : Fin n1 × Fin n2,
              (fun (w : Fin n1 × Fin n2) (x : ℝ) => bc w * (2 * x - 1))
                w (if w ∈ eps then (1:ℝ) else 0)) := by
          funext eps
          rw [hL]
          apply Finset.sum_congr rfl; intro w _
          have hs : rademacherSign eps w.1 w.2
              = 2 * (if w ∈ eps then (1:ℝ) else 0) - 1 := by
            unfold rademacherSign
            by_cases hm : (w.1, w.2) ∈ eps
            · have : w ∈ eps := by simpa using hm
              simp [hm, this]; norm_num
            · have : w ∉ eps := by simpa using hm
              simp [hm, this]
          rw [hs]
        rw [hLind, rademacher_expectation_eq_bernoulli_half_expectation]
        rw [bernoulli_powerset_expectation_linear ((1:ℝ)/2)
          (fun (w : Fin n1 × Fin n2) (x : ℝ) => bc w * (2 * x - 1))]
        apply Finset.sum_eq_zero; intro w _; norm_num
      -- BILINEAR half = 0
      have hBmean : rademacherExpectation Bl = 0 := by
        set G : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → ℝ → ℝ → ℝ :=
          fun w1 w2 x y =>
            if w1 = w2 then (0 : ℝ)
            else ac w1 w2 * (2 * x - 1) * (2 * y - 1) with hG
        have hBind : Bl = (fun eps =>
            ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
              G w1 w2 (if w1 ∈ eps then (1:ℝ) else 0) (if w2 ∈ eps then (1:ℝ) else 0)) := by
          funext eps
          rw [hBl]
          refine Finset.sum_congr rfl (fun w1 _ => ?_)
          refine Finset.sum_congr rfl (fun w2 _ => ?_)
          by_cases h : w1 = w2
          · simp [hG, h]
          · simp only [hG, if_neg h]
            have hs1 : rademacherSign eps w1.1 w1.2
                = 2 * (if w1 ∈ eps then (1:ℝ) else 0) - 1 := by
              unfold rademacherSign
              by_cases hm : (w1.1, w1.2) ∈ eps
              · have : w1 ∈ eps := by simpa using hm
                simp [hm, this]; norm_num
              · have : w1 ∉ eps := by simpa using hm
                simp [hm, this]
            have hs2 : rademacherSign eps w2.1 w2.2
                = 2 * (if w2 ∈ eps then (1:ℝ) else 0) - 1 := by
              unfold rademacherSign
              by_cases hm : (w2.1, w2.2) ∈ eps
              · have : w2 ∈ eps := by simpa using hm
                simp [hm, this]; norm_num
              · have : w2 ∉ eps := by simpa using hm
                simp [hm, this]
            rw [hs1, hs2]
        rw [hBind, rademacher_expectation_eq_bernoulli_half_expectation]
        rw [bernoulli_powerset_expectation_double]
        apply Finset.sum_eq_zero; intro w1 _
        apply Finset.sum_eq_zero; intro w2 _
        by_cases h : w1 = w2
        · have hz : (fun Omega : Finset (Fin n1 × Fin n2) =>
              G w1 w2 (if w1 ∈ Omega then (1:ℝ) else 0)
              (if w2 ∈ Omega then (1:ℝ) else 0)) = (fun _ => (0:ℝ)) := by
            funext Omega; simp [hG, h]
          rw [hz]; simp [bernoulliExpectation]
        · have hpair := bernoulli_powerset_expectation_pair_coordinate
            ((1:ℝ)/2) w1 w2 h (fun x => ac w1 w2 * (2 * x - 1)) (fun y => 2 * y - 1)
          have hbody :
              (fun Omega : Finset (Fin n1 × Fin n2) =>
                  G w1 w2 (if w1 ∈ Omega then (1:ℝ) else 0)
                  (if w2 ∈ Omega then (1:ℝ) else 0))
              = (fun Omega : Finset (Fin n1 × Fin n2) =>
                  (fun x => ac w1 w2 * (2 * x - 1)) (if w1 ∈ Omega then (1:ℝ) else 0)
                  * (fun y => 2 * y - 1) (if w2 ∈ Omega then (1:ℝ) else 0)) := by
            funext Omega; simp only [hG, if_neg h]
          rw [hbody, hpair]; norm_num
      rw [hLmean, hBmean]; ring
    rw [hFsplit]; exact hLBmean
  -- CASE SPLIT on the σ-variance of F.
  by_cases hvar : 0 < rademacherExpectation (fun eps => (F eps) ^ 2)
  · -- positive variance: mixed conditional Lemma 2
    have := dlp_conditional_lemma2_sigma_fiber_mixed_chaos_inl b a T xv yv hxv hyv hnorm
      (by simpa [hF, mchaos] using hmean)
      (by simpa [hF, mchaos] using hvar)
    simpa [mchaos] using this
  · -- degenerate variance: E[F²] = 0 ⇒ each F eps = 0 ⇒ survival indicator ≡ 1
    push_neg at hvar
    have hsum0 : rademacherExpectation (fun eps => (F eps) ^ 2) = 0 := by
      have hnn : 0 ≤ rademacherExpectation (fun eps => (F eps) ^ 2) := by
        unfold rademacherExpectation rademacherObservationWeight
        apply Finset.sum_nonneg; intro eps _; positivity
      linarith
    have hterm0 : ∀ eps : Finset (Fin n1 × Fin n2), F eps = 0 := by
      intro eps
      have hz : rademacherObservationWeight eps * (F eps) ^ 2 = 0 := by
        have hsumnn : ∀ e : Finset (Fin n1 × Fin n2),
            e ∈ (Finset.univ : Finset (Finset (Fin n1 × Fin n2))) →
            0 ≤ rademacherObservationWeight e * (F e) ^ 2 := by
          intro e _; unfold rademacherObservationWeight; positivity
        have := (Finset.sum_eq_zero_iff_of_nonneg hsumnn).mp
          (by simpa [rademacherExpectation] using hsum0)
        exact this eps (Finset.mem_univ eps)
      have hw : (0:ℝ) < rademacherObservationWeight eps := by
        unfold rademacherObservationWeight; positivity
      have : (F eps) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hz with h | h
        · exact absurd h (ne_of_gt hw)
        · exact h
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    -- survival indicator ≡ 1 via the pairing/degenerate argument
    have hsurv : ∀ eps : Finset (Fin n1 × Fin n2),
        spectralNorm T ≤ spectralNorm (T + mchaos b a eps) := by
      intro eps
      rw [← hnorm]
      have hFe0 : F eps = 0 := hterm0 eps
      have hsplit :
          ⟪Matrix.toEuclideanLin (T + mchaos b a eps) xv, yv⟫_ℝ
            = ⟪Matrix.toEuclideanLin T xv, yv⟫_ℝ + F eps := by
        simp only [hF, map_add]
        rw [LinearMap.add_apply, inner_add_left]
      have hub :
          ⟪Matrix.toEuclideanLin (T + mchaos b a eps) xv, yv⟫_ℝ
            ≤ spectralNorm (T + mchaos b a eps) * ‖xv‖ * ‖yv‖ :=
        spectral_norm_inner_pairing_bound (T + mchaos b a eps) xv yv
      have hsp_nonneg : 0 ≤ spectralNorm (T + mchaos b a eps) := by
        rw [spectralNorm]; exact norm_nonneg _
      have hle1 :
          ⟪Matrix.toEuclideanLin T xv, yv⟫_ℝ
            ≤ ⟪Matrix.toEuclideanLin (T + mchaos b a eps) xv, yv⟫_ℝ := by
        rw [hsplit, hFe0]; linarith
      calc ⟪Matrix.toEuclideanLin T xv, yv⟫_ℝ
          ≤ ⟪Matrix.toEuclideanLin (T + mchaos b a eps) xv, yv⟫_ℝ := hle1
        _ ≤ spectralNorm (T + mchaos b a eps) * ‖xv‖ * ‖yv‖ := hub
        _ ≤ spectralNorm (T + mchaos b a eps) * 1 * 1 := by
              apply mul_le_mul
              · apply mul_le_mul_of_nonneg_left hxv hsp_nonneg
              · exact hyv
              · exact norm_nonneg _
              · positivity
        _ = spectralNorm (T + mchaos b a eps) := by ring
    -- rademacherExpectation of the constant-1 indicator = 1 ≥ 1/324
    have hval : rademacherExpectation
        (fun eps =>
          if spectralNorm T ≤ spectralNorm (T + mchaos b a eps)
          then (1 : ℝ) else 0) = 1 := by
      unfold rademacherExpectation rademacherObservationWeight
      have hterm : ∀ eps : Finset (Fin n1 × Fin n2),
          ((1:ℝ)/2) ^ Fintype.card (Fin n1 × Fin n2)
            * (if spectralNorm T ≤ spectralNorm (T + mchaos b a eps) then (1:ℝ) else 0)
            = ((1:ℝ)/2) ^ Fintype.card (Fin n1 × Fin n2) := by
        intro eps; rw [if_pos (hsurv eps)]; ring
      rw [Finset.sum_congr rfl (fun eps _ => hterm eps)]
      rw [Finset.sum_const, Finset.card_univ]
      rw [nsmul_eq_mul]
      have hcard : (Fintype.card (Finset (Fin n1 × Fin n2)) : ℝ)
          = 2 ^ Fintype.card (Fin n1 × Fin n2) := by
        rw [Fintype.card_finset]; push_cast; ring
      rw [hcard]
      rw [← mul_pow]; norm_num
    have hgoal :
        rademacherExpectation
            (fun eps =>
              if spectralNorm T ≤ spectralNorm (T + mchaos b a eps)
              then (1 : ℝ) else 0) ≥ 1 / 324 := by rw [hval]; norm_num
    simpa [mchaos] using hgoal
