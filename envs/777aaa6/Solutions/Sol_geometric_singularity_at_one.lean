-- Prove2me | solution 1 for geometric_singularity_at_one
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-27T04:34:48.458998+00:00
-- url     : https://prove2.me/submissions/7eb65bbf-a01c-4301-81d1-cd083908586e

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Pringsheim
import Mathlib
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Filter
open scoped NNReal ENNReal Topology BigOperators

noncomputable section

namespace FormalMultilinearSeries

private lemma card_finset_fin_card_eq (k l : ℕ) :
    Fintype.card {s : Finset (Fin (k + l)) // s.card = l} = Nat.choose (k + l) l := by
  rw [Fintype.card_of_subtype (Finset.powersetCard l Finset.univ) (by intro s; simp)]
  simp

private lemma scalar_changeOriginSeries_eval_one
    (c : ℕ → ℂ) (x : ℂ) (k l : ℕ) :
    ((FormalMultilinearSeries.ofScalars ℂ c).changeOriginSeries k l (fun _ => x))
      (fun _ => (1 : ℂ)) =
        (Nat.choose (k + l) k : ℂ) * c (k + l) * x ^ l := by
  unfold FormalMultilinearSeries.changeOriginSeries
  simp_rw [ContinuousMultilinearMap.sum_apply]
  simp_rw [FormalMultilinearSeries.changeOriginSeriesTerm_apply]
  simp_rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff]
  simp_rw [FormalMultilinearSeries.coeff_ofScalars]
  simp_rw [smul_eq_mul]
  have hprod (s : Finset (Fin (k + l))) (hs : s.card = l) :
      (∏ i : Fin (k + l), s.piecewise (fun _ => x) (fun _ => (1 : ℂ)) i) = x ^ l := by
    change (∏ i ∈ (Finset.univ : Finset (Fin (k + l))),
      s.piecewise (fun _ => x) (fun _ => (1 : ℂ)) i) = x ^ l
    rw [Finset.prod_piecewise]
    simp [hs]
  have hprod' (s : {s : Finset (Fin (k + l)) // s.card = l}) :
      (∏ i : Fin (k + l), (s : Finset (Fin (k + l))).piecewise
        (fun _ => x) (fun _ => (1 : ℂ)) i) = x ^ l :=
    hprod s.1 s.2
  simp_rw [hprod']
  rw [Finset.sum_const]
  rw [nsmul_eq_mul]
  rw [Finset.card_univ]
  rw [card_finset_fin_card_eq]
  rw [Nat.choose_symm_add]
  ring_nf

lemma ofScalars_changeOrigin_coeff
    (c : ℕ → ℂ) (x : ℂ) (k : ℕ)
    (hx : (‖x‖₊ : ℝ≥0∞) <
      (FormalMultilinearSeries.ofScalars ℂ c).radius) :
    ((FormalMultilinearSeries.ofScalars ℂ c).changeOrigin x).coeff k =
      ∑' l : ℕ, (Nat.choose (k + l) k : ℂ) * c (k + l) * x ^ l := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ c
  have hr : 0 < p.radius := lt_of_le_of_lt (zero_le _) hx
  have hxmem : x ∈ Metric.eball (0 : ℂ) p.radius := mem_eball_zero_iff.2 hx
  have hs := (p.hasFPowerSeriesOnBall_changeOrigin k hr).hasSum hxmem
  rw [zero_add] at hs
  rw [FormalMultilinearSeries.coeff]
  calc
    (p.changeOrigin x k) (fun _ : Fin k => (1 : ℂ))
        = ∑' l : ℕ,
            (p.changeOriginSeries k l (fun _ => x)) (fun _ : Fin k => (1 : ℂ)) :=
          (ContinuousMultilinearMap.hasSum_eval hs
            (fun _ : Fin k => (1 : ℂ))).tsum_eq.symm
    _ = ∑' l : ℕ,
          (Nat.choose (k + l) k : ℂ) * c (k + l) * x ^ l := by
          apply tsum_congr
          intro l
          simpa [p] using scalar_changeOriginSeries_eval_one c x k l

lemma ofScalars_changeOrigin_nnnorm
    (a : ℕ → ℝ≥0) (r0 : ℝ≥0) (k : ℕ)
    (hr0 : (r0 : ℝ≥0∞) <
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius) :
    ‖((FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).changeOrigin
        ((r0 : ℝ) : ℂ) k)‖₊ =
      ∑' l : ℕ, (Nat.choose (k + l) k : ℝ≥0) * a (k + l) * r0 ^ l := by
  let b : ℕ → ℝ≥0 := fun l => (Nat.choose (k + l) k : ℝ≥0) * a (k + l) * r0 ^ l
  have hcomplex :
      (∑' l : ℕ, (Nat.choose (k + l) k : ℂ) * (a (k + l) : ℂ) *
          (((r0 : ℝ) : ℂ) ^ l)) = (((∑' l : ℕ, b l) : ℝ≥0) : ℂ) := by
    calc
      (∑' l : ℕ, (Nat.choose (k + l) k : ℂ) * (a (k + l) : ℂ) *
          (((r0 : ℝ) : ℂ) ^ l))
          = ∑' l : ℕ, (((b l : ℝ≥0) : ℝ) : ℂ) := by
            apply tsum_congr
            intro l
            simp [b, NNReal.coe_natCast]
      _ = (((∑' l : ℕ, ((b l : ℝ≥0) : ℝ)) : ℝ) : ℂ) := by
            exact (Complex.ofReal_tsum (fun l : ℕ => ((b l : ℝ≥0) : ℝ))).symm
      _ = (((∑' l : ℕ, b l) : ℝ≥0) : ℂ) := by
            rw [NNReal.coe_tsum]
  apply NNReal.eq
  rw [coe_nnnorm]
  rw [FormalMultilinearSeries.norm_apply_eq_norm_coef]
  rw [ofScalars_changeOrigin_coeff (fun n => (a n : ℂ)) ((r0 : ℝ) : ℂ) k]
  · rw [hcomplex]
    simp [b]
  · simpa using hr0

private lemma nnnorm_ofScalars_nnreal (a : ℕ → ℝ≥0) (n : ℕ) :
    ‖(FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ)) n)‖₊ = a n := by
  apply NNReal.eq
  simp

lemma inner_summable_changeOrigin_coeff_base
    (a : ℕ → ℝ≥0) (r0 : ℝ≥0) (k : ℕ)
    (hr0 : (r0 : ℝ≥0∞) <
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius) :
    Summable fun l : ℕ =>
      (Nat.choose (k + l) k : ℝ≥0) * a (k + l) * r0 ^ l := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))
  have hsigma := p.changeOriginSeries_summable_aux₂ hr0 k
  have houter := (NNReal.summable_sigma.1 hsigma).2
  refine houter.congr ?_
  intro l
  have hfinite :
      (∑' s : {s : Finset (Fin (k + l)) // s.card = l}, ‖p (k + l)‖₊ * r0 ^ l) =
        (Nat.choose (k + l) k : ℝ≥0) * a (k + l) * r0 ^ l := by
    rw [tsum_fintype]
    rw [Finset.sum_const]
    rw [nsmul_eq_mul]
    rw [Finset.card_univ]
    rw [card_finset_fin_card_eq]
    rw [Nat.choose_symm_add]
    simp [p, nnnorm_ofScalars_nnreal, mul_assoc]
  simpa only [Sigma.fst] using hfinite

lemma summable_original_of_sigma
    (a : ℕ → ℝ≥0) (r0 t : ℝ≥0)
    (hsigma : Summable fun p : (Σ _ : ℕ, ℕ) =>
      (Nat.choose (p.1 + p.2) p.1 : ℝ≥0) * a (p.1 + p.2) *
        r0 ^ p.2 * t ^ p.1) :
    Summable fun n => a n * (r0 + t) ^ n := by
  let F : ℕ → ℕ → ℝ≥0 := fun k l =>
    (Nat.choose (k + l) k : ℝ≥0) * a (k + l) * r0 ^ l * t ^ k
  have hsigma' : Summable fun p : (Σ _ : ℕ, ℕ) => F p.1 p.2 := by
    simpa [F, mul_assoc] using hsigma
  let e : (Σ n : ℕ, Finset.antidiagonal n) ≃ (Σ _ : ℕ, ℕ) :=
    Finset.sigmaAntidiagonalEquivProd.trans (Equiv.sigmaEquivProd ℕ ℕ).symm
  have hant : Summable fun p : (Σ n : ℕ, Finset.antidiagonal n) =>
      F (p.2 : ℕ × ℕ).1 (p.2 : ℕ × ℕ).2 := by
    simpa [e, F] using (e.summable_iff.2 hsigma')
  have houter := (NNReal.summable_sigma.1 hant).2
  refine houter.congr ?_
  intro n
  have hcollapse :
      (∑ kl ∈ Finset.antidiagonal n,
          a n * (Nat.choose n kl.1 : ℝ≥0) * r0 ^ kl.2 * t ^ kl.1) =
        a n * (r0 + t) ^ n := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k l => a n * (Nat.choose n k : ℝ≥0) * r0 ^ l * t ^ k) n]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    rw [add_comm r0 t, add_pow]
    simp [mul_comm, mul_assoc]
  have htsum :
      (∑' kl : Finset.antidiagonal n, F (kl : ℕ × ℕ).1 (kl : ℕ × ℕ).2) =
        a n * (r0 + t) ^ n := by
    rw [tsum_fintype]
    calc
      (∑ b : Finset.antidiagonal n, F (b : ℕ × ℕ).1 (b : ℕ × ℕ).2)
          = ∑ kl ∈ Finset.antidiagonal n, F kl.1 kl.2 :=
            Finset.sum_finset_coe (fun kl : ℕ × ℕ => F kl.1 kl.2) (Finset.antidiagonal n)
      _ = ∑ kl ∈ Finset.antidiagonal n,
            a n * (Nat.choose n kl.1 : ℝ≥0) * r0 ^ kl.2 * t ^ kl.1 := by
            apply Finset.sum_congr rfl
            intro kl hkl
            have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
            simp [F, hsum, mul_comm, mul_left_comm]
      _ = a n * (r0 + t) ^ n := hcollapse
  simpa using htsum

lemma sigma_summable_changeOrigin_coeff
    (a : ℕ → ℝ≥0) {r0 t : ℝ≥0}
    (hr0 : (r0 : ℝ≥0∞) <
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius)
    (ht : (t : ℝ≥0∞) <
      ((FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).changeOrigin
        ((r0 : ℝ) : ℂ)).radius) :
    Summable fun p : (Σ _ : ℕ, ℕ) =>
      (Nat.choose (p.1 + p.2) p.1 : ℝ≥0) * a (p.1 + p.2) *
        r0 ^ p.2 * t ^ p.1 := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))
  let base : ℕ → ℕ → ℝ≥0 := fun k l =>
    (Nat.choose (k + l) k : ℝ≥0) * a (k + l) * r0 ^ l
  have hinner : ∀ k : ℕ, Summable fun l : ℕ => base k l * t ^ k := by
    intro k
    exact (inner_summable_changeOrigin_coeff_base a r0 k hr0).mul_right (t ^ k)
  have hchange : Summable fun k : ℕ => ‖p.changeOrigin ((r0 : ℝ) : ℂ) k‖₊ * t ^ k := by
    exact (p.changeOrigin ((r0 : ℝ) : ℂ)).summable_nnnorm_mul_pow ht
  have houter : Summable fun k : ℕ => ∑' l : ℕ, base k l * t ^ k := by
    refine hchange.congr ?_
    intro k
    rw [ofScalars_changeOrigin_nnnorm a r0 k]
    · rw [NNReal.tsum_mul_right]
    · simpa [p] using hr0
  have hsigma : Summable fun q : (Σ _ : ℕ, ℕ) => base q.1 q.2 * t ^ q.1 :=
    NNReal.summable_sigma.2 ⟨hinner, houter⟩
  simpa [base, mul_assoc] using hsigma

lemma summable_original_of_summable_changeOrigin
    (a : ℕ → ℝ≥0) {r0 t : ℝ≥0}
    (hr0 : (r0 : ℝ≥0∞) <
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius)
    (ht : (t : ℝ≥0∞) <
      ((FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).changeOrigin
        ((r0 : ℝ) : ℂ)).radius) :
    Summable fun n => a n * (r0 + t) ^ n :=
  by
    exact summable_original_of_sigma a r0 t
      (sigma_summable_changeOrigin_coeff (a := a) (r0 := r0) (t := t) hr0 ht)

lemma le_radius_add_of_lt_changeOrigin_radius_of_nonneg
    (a : ℕ → ℝ≥0) {r0 t : ℝ≥0} :
    let p : FormalMultilinearSeries ℂ ℂ ℂ :=
      FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))
    (r0 : ℝ≥0∞) < p.radius →
    (t : ℝ≥0∞) < (p.changeOrigin ((r0 : ℝ) : ℂ)).radius →
      ((r0 + t : ℝ≥0) : ℝ≥0∞) ≤ p.radius := by
  dsimp
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))
  intro hr0 ht
  apply p.le_radius_of_summable_nnnorm
  have hs : Summable fun n : ℕ => a n * (r0 + t) ^ n :=
    summable_original_of_summable_changeOrigin (a := a) (r0 := r0) (t := t) hr0 ht
  refine hs.congr ?_
  intro n
  simp [p, nnnorm_ofScalars_nnreal]

end FormalMultilinearSeries
end

open Filter
open scoped NNReal ENNReal Topology

noncomputable section

private lemma nnreal_quarter_pos {x : ℝ≥0} (hx : 0 < x) :
    0 < x / 4 := by
  positivity

private lemma nnreal_two_mul_quarter_lt {x : ℝ≥0} (hx : 0 < x) :
    x / 4 + x / 4 < x := by
  rw [← NNReal.coe_lt_coe]
  simp
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  nlinarith

private lemma nnreal_quarter_lt {x : ℝ≥0} (hx : 0 < x) :
    x / 4 < x := by
  have h := nnreal_two_mul_quarter_lt (x := x) hx
  exact lt_of_le_of_lt (by simp) h

private lemma sub_lt_self_nnreal {R ε : ℝ≥0} (hR : 0 < R) (hε : 0 < ε) :
    R - ε < R := by
  rw [← NNReal.coe_lt_coe]
  by_cases hεR : ε ≤ R
  · rw [NNReal.coe_sub hεR]
    have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    linarith
  · have hR' : (0 : ℝ) < R := by exact_mod_cast hR
    have hsub : R - ε = 0 := tsub_eq_zero_of_le (le_of_not_ge hεR)
    simp [hsub, hR']

private lemma radius_pos_of_radius_eq
    (a : ℕ → ℝ≥0) {R : ℝ≥0} (hRpos : 0 < R)
    (hR : (pringsheimSeries a).radius = (R : ℝ≥0∞)) :
    0 < (pringsheimSeries a).radius := by
  rw [hR]
  exact ENNReal.coe_pos.2 hRpos

private lemma shifted_radius_gt
    (a : ℕ → ℝ≥0) {R ε : ℝ≥0} {g : ℂ → ℂ}
    {q : FormalMultilinearSeries ℂ ℂ ℂ} {δ : ℝ≥0∞}
    (hRpos : 0 < R)
    (hR : (pringsheimSeries a).radius = (R : ℝ≥0∞))
    (hεpos : 0 < ε) (hεR : ε < R)
    (hg : HasFPowerSeriesOnBall g q (((R : ℝ) : ℂ)) δ)
    (hεεδ : ((ε + ε : ℝ≥0) : ℝ≥0∞) < δ)
    (heq : (pringsheimSeries a).sum =ᶠ[𝓝 (((R - ε : ℝ≥0) : ℝ) : ℂ)] g) :
    (ε : ℝ≥0∞) <
      ((pringsheimSeries a).changeOrigin (((R - ε : ℝ≥0) : ℝ) : ℂ)).radius := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := pringsheimSeries a
  let r0 : ℝ≥0 := R - ε
  let zR : ℂ := ((R : ℝ) : ℂ)
  let z0 : ℂ := ((r0 : ℝ) : ℂ)
  let y : ℂ := -(((ε : ℝ) : ℂ))
  have hy_norm : ‖y‖₊ = ε := by
    simp [y]
  have hcenter : zR + y = z0 := by
    have hεRle : ε ≤ R := hεR.le
    have hz0 : z0 = zR - (((ε : ℝ) : ℂ)) := by
      simp [z0, zR, r0, NNReal.coe_sub hεRle]
    calc
      zR + y = zR - (((ε : ℝ) : ℂ)) := by simp [y, sub_eq_add_neg]
      _ = z0 := hz0.symm
  have hεδ : (‖y‖₊ : ℝ≥0∞) < δ := by
    rw [hy_norm]
    exact (ENNReal.coe_le_coe.2 (by simp : ε ≤ ε + ε)).trans_lt hεεδ
  have hgShift₀ : HasFPowerSeriesOnBall g (q.changeOrigin y) (zR + y) (δ - ‖y‖₊) :=
    hg.changeOrigin hεδ
  have hgShift : HasFPowerSeriesOnBall g (q.changeOrigin y) z0 (δ - (ε : ℝ≥0∞)) := by
    simpa [hcenter, hy_norm] using hgShift₀
  have hp0 : HasFPowerSeriesOnBall p.sum p (0 : ℂ) p.radius := by
    exact FormalMultilinearSeries.hasFPowerSeriesOnBall p
      (by simpa [p] using radius_pos_of_radius_eq a hRpos hR)
  have hr0_lt_R : r0 < R := by
    exact sub_lt_self_nnreal hRpos hεpos
  have hr0_lt_radius : (r0 : ℝ≥0∞) < p.radius := by
    simpa [p, hR] using ENNReal.coe_lt_coe.2 hr0_lt_R
  have hz0_norm : ‖z0‖₊ = r0 := by
    simp [z0]
  have hpShift₀ :
      HasFPowerSeriesOnBall p.sum (p.changeOrigin z0) ((0 : ℂ) + z0)
        (p.radius - ‖z0‖₊) :=
    hp0.changeOrigin (by simpa [hz0_norm] using hr0_lt_radius)
  have hpShift :
      HasFPowerSeriesOnBall p.sum (p.changeOrigin z0) z0
        (p.radius - (r0 : ℝ≥0∞)) := by
    simpa [hz0_norm] using hpShift₀
  have hseries :
      p.changeOrigin z0 = q.changeOrigin y :=
    hpShift.hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
      hgShift.hasFPowerSeriesAt (by simpa [p, z0, r0] using heq)
  have hlarge :
      δ - (ε : ℝ≥0∞) ≤ (p.changeOrigin z0).radius := by
    simpa [hseries] using hgShift.r_le
  have hε_lt_sub : (ε : ℝ≥0∞) < δ - (ε : ℝ≥0∞) := by
    rw [lt_tsub_iff_right]
    simpa using hεεδ
  exact hε_lt_sub.trans_le (by simpa [p, z0, r0] using hlarge)

private lemma contradiction_of_shifted_radius_gt
    (a : ℕ → ℝ≥0) {R ε : ℝ≥0}
    (hRpos : 0 < R)
    (hR : (pringsheimSeries a).radius = (R : ℝ≥0∞))
    (hεpos : 0 < ε) (hεR : ε < R)
    (hshift :
      (ε : ℝ≥0∞) <
        ((pringsheimSeries a).changeOrigin (((R - ε : ℝ≥0) : ℝ) : ℂ)).radius) :
    False := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := pringsheimSeries a
  let r0 : ℝ≥0 := R - ε
  obtain ⟨t, hεt, ht⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hshift
  have hr0_lt_R : r0 < R := sub_lt_self_nnreal hRpos hεpos
  have hr0_lt_radius : (r0 : ℝ≥0∞) < p.radius := by
    simpa [p, hR] using ENNReal.coe_lt_coe.2 hr0_lt_R
  have hcore :
      ((r0 + t : ℝ≥0) : ℝ≥0∞) ≤ p.radius := by
    exact FormalMultilinearSeries.le_radius_add_of_lt_changeOrigin_radius_of_nonneg
      (a := a) (r0 := r0) (t := t) hr0_lt_radius
      (by simpa [p, r0] using ht)
  have hleR : ((r0 + t : ℝ≥0) : ℝ≥0∞) ≤ (R : ℝ≥0∞) := by
    simpa [p, hR] using hcore
  have hεt_nn : ε < t := ENNReal.coe_lt_coe.1 hεt
  have hR_lt_r0t : R < r0 + t := by
    rw [← NNReal.coe_lt_coe]
    have hεRle : ε ≤ R := hεR.le
    rw [NNReal.coe_add, NNReal.coe_sub hεRle]
    have hεt' : (ε : ℝ) < t := by exact_mod_cast hεt_nn
    linarith
  exact (not_lt_of_ge hleR) (ENNReal.coe_lt_coe.2 hR_lt_r0t)

private lemma choose_epsilon_two_lt
    {R δ₀ : ℝ≥0} (hRpos : 0 < R) (hδpos : 0 < δ₀) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ε < R ∧ ε + ε < δ₀ := by
  let m : ℝ≥0 := min R δ₀
  have hmpos : 0 < m := by
    change (0 : ℝ≥0) < min R δ₀
    exact lt_min hRpos hδpos
  refine ⟨m / 4, nnreal_quarter_pos hmpos, ?_, ?_⟩
  · exact (nnreal_quarter_lt hmpos).trans_le (min_le_left _ _)
  · exact (nnreal_two_mul_quarter_lt hmpos).trans_le (min_le_right _ _)

theorem pringsheim_not_analyticAt
    (a : ℕ → ℝ≥0) {R : ℝ≥0} (hRpos : 0 < R)
    (hR :
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius =
        (R : ℝ≥0∞)) :
    ¬ AnalyticAt ℂ
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).sum
      (((R : ℝ) : ℂ)) := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := pringsheimSeries a
  change ¬ AnalyticAt ℂ p.sum (((R : ℝ) : ℂ))
  intro h
  obtain ⟨q, δ, hq⟩ := h
  obtain ⟨δ₀, hδ₀posE, hδ₀δ⟩ :=
    ENNReal.lt_iff_exists_nnreal_btwn.1 hq.r_pos
  have hδ₀pos : 0 < δ₀ := by
    simpa using hδ₀posE
  obtain ⟨ε, hεpos, hεR, hεεδ₀⟩ :=
    choose_epsilon_two_lt (R := R) (δ₀ := δ₀) hRpos hδ₀pos
  have hεεδ : ((ε + ε : ℝ≥0) : ℝ≥0∞) < δ :=
    (ENNReal.coe_lt_coe.2 hεεδ₀).trans hδ₀δ
  have hshift :
      (ε : ℝ≥0∞) <
        ((pringsheimSeries a).changeOrigin (((R - ε : ℝ≥0) : ℝ) : ℂ)).radius := by
    apply shifted_radius_gt (a := a) (R := R) (ε := ε) (g := p.sum)
      (q := q) (δ := δ) hRpos
    · simpa [p] using hR
    · exact hεpos
    · exact hεR
    · simpa [p] using hq
    · exact hεεδ
    · exact Eventually.of_forall fun _ => rfl
  exact contradiction_of_shifted_radius_gt (a := a) (R := R) (ε := ε)
    hRpos (by simpa using hR) hεpos hεR hshift

end

open Filter
open scoped NNReal ENNReal Topology

noncomputable section

/-- The all-ones ordinary generating function has radius of convergence `1`. -/
theorem geometric_radius_eq_one :
    (FormalMultilinearSeries.ofScalars ℂ (fun _ : ℕ => (1 : ℂ))).radius =
      (1 : ℝ≥0∞) := by
  simpa using
    (FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto ℂ
      (fun _ : ℕ => (1 : ℂ)) (r := (1 : ℝ≥0)) one_ne_zero (by simp))

end

open Filter
open scoped NNReal ENNReal Topology
theorem solution :
    ¬ AnalyticAt ℂ
      (FormalMultilinearSeries.ofScalars ℂ (fun _ : ℕ => (1 : ℂ))).sum
      (1 : ℂ) := by
  simpa using
    (pringsheim_not_analyticAt (fun _ : ℕ => (1 : ℝ≥0))
      (R := (1 : ℝ≥0)) zero_lt_one geometric_radius_eq_one)
