-- Prove2me | solution 1 for BanditAlgorithm.bernoulliRelativeEntropy_antitone_fst
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T04:54:49.262502+00:00
-- url     : https://prove2.me/submissions/08f692eb-5bcb-44e0-978b-053c8f8a2fad

import Definitions.Def_bernoulliRelativeEntropy
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open Set Filter Topology

namespace BanditAlgorithm

private noncomputable def klFstExpanded (q p : ℝ) : ℝ :=
  p * Real.log p + (1 - p) * Real.log (1 - p) -
    p * Real.log q - (1 - p) * Real.log (1 - q)

private lemma klFstExpanded_eq
    {p q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    klFstExpanded q p = bernoulliRelativeEntropy p q := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [klFstExpanded, bernoulliRelativeEntropy]
  rcases eq_or_ne p 1 with rfl | hp1
  · simp [klFstExpanded, bernoulliRelativeEntropy]
  rw [klFstExpanded, bernoulliRelativeEntropy,
    Real.log_div hp0 (ne_of_gt hq.1),
    Real.log_div (sub_ne_zero.mpr hp1.symm)
      (sub_ne_zero.mpr (ne_of_lt hq.2).symm)]
  ring

private lemma continuous_klFstExpanded (q : ℝ) :
    Continuous (klFstExpanded q) := by
  unfold klFstExpanded
  have h1 : Continuous (fun p : ℝ ↦ p * Real.log p) :=
    Real.continuous_mul_log
  have h2 : Continuous (fun p : ℝ ↦
      (1 - p) * Real.log (1 - p)) :=
    Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
  fun_prop

private lemma hasDerivAt_klFstExpanded
    {p q : ℝ} (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    HasDerivAt (klFstExpanded q)
      (Real.log p - Real.log (1 - p) -
        Real.log q + Real.log (1 - q)) p := by
  unfold klFstExpanded
  have hfirst := Real.hasDerivAt_mul_log hp0
  have honeSub : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) p := by
    simpa only [Pi.sub_apply, id_eq, zero_sub] using
      (hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)
  have hsecond :
      HasDerivAt (fun x : ℝ ↦ (1 - x) * Real.log (1 - x))
        (-(Real.log (1 - p) + 1)) p := by
    convert (Real.hasDerivAt_mul_log
      (sub_ne_zero.mpr hp1.symm)).comp p honeSub using 1
    ring
  have hthird :
      HasDerivAt (fun x : ℝ ↦ x * Real.log q) (Real.log q) p := by
    convert (hasDerivAt_id p).mul_const (Real.log q) using 1 <;> ring
  have hfourth :
      HasDerivAt (fun x : ℝ ↦ (1 - x) * Real.log (1 - q))
        (-Real.log (1 - q)) p := by
    convert honeSub.mul_const (Real.log (1 - q)) using 1 <;> ring
  convert ((hfirst.add hsecond).sub hthird).sub hfourth using 1 <;> ring

private lemma klFstExpanded_deriv_nonpos
    {p q : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpq : p ≤ q) (hq : q ∈ Ioo (0 : ℝ) 1) :
    deriv (klFstExpanded q) p ≤ 0 := by
  rw [(hasDerivAt_klFstExpanded
    (ne_of_gt hp.1) (ne_of_lt hp.2)).deriv]
  have hratio :
      p / (1 - p) ≤ q / (1 - q) := by
    rw [div_le_div_iff₀ (sub_pos.mpr hp.2) (sub_pos.mpr hq.2)]
    nlinarith
  have hlog :
      Real.log (p / (1 - p)) ≤ Real.log (q / (1 - q)) :=
    Real.strictMonoOn_log.monotoneOn
      (div_pos hp.1 (sub_pos.mpr hp.2))
      (div_pos hq.1 (sub_pos.mpr hq.2)) hratio
  rw [Real.log_div (ne_of_gt hp.1)
      (sub_ne_zero.mpr (ne_of_lt hp.2).symm),
    Real.log_div (ne_of_gt hq.1)
      (sub_ne_zero.mpr (ne_of_lt hq.2).symm)] at hlog
  linarith

end BanditAlgorithm

open BanditAlgorithm

theorem solution
    {x y q : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hxy : x ≤ y) (hyq : y ≤ q) (hq : q ∈ Ioo (0 : ℝ) 1) :
    BanditAlgorithm.bernoulliRelativeEntropy y q ≤
      BanditAlgorithm.bernoulliRelativeEntropy x q := by
  rw [← klFstExpanded_eq hq, ← klFstExpanded_eq hq]
  have hcont : ContinuousOn (klFstExpanded q) (Icc x y) :=
    (continuous_klFstExpanded q).continuousOn
  have hdiff : DifferentiableOn ℝ (klFstExpanded q)
      (interior (Icc x y)) := by
    intro z hz
    have hz' : z ∈ Ioo x y := by
      simpa [interior_Icc, hxy] using hz
    rcases hz' with ⟨hzx, hzy⟩
    have hx0 : 0 ≤ x := hx.1
    have hy1 : y < 1 := hyq.trans_lt hq.2
    exact (hasDerivAt_klFstExpanded
      (by linarith) (by linarith))
        |>.differentiableAt.differentiableWithinAt
  have hderiv : ∀ z ∈ interior (Icc x y),
      deriv (klFstExpanded q) z ≤ 0 := by
    intro z hz
    have hz' : z ∈ Ioo x y := by
      simpa [interior_Icc, hxy] using hz
    rcases hz' with ⟨hzx, hzy⟩
    have hx0 : 0 ≤ x := hx.1
    have hy1 : y < 1 := hyq.trans_lt hq.2
    apply klFstExpanded_deriv_nonpos
    · exact ⟨by linarith, by linarith⟩
    · linarith
    · exact hq
  exact (antitoneOn_of_deriv_nonpos (convex_Icc x y)
      hcont hdiff hderiv)
    (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy
