-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T11:35:29.879571+00:00
-- url     : https://prove2.me/submissions/34e77e51-0af4-4270-b872-8ee058e8f228

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Definitions.Def_erdos390_analytic_foundations_001
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

set_option autoImplicit false

universe u_1 u_2

namespace Sol767

open Erdos390.Full

theorem absDelta_le {Ω : Type*} [Fintype Ω] (P Q : FiniteProbability Ω) (d A : ℝ)
    (hTV : ∑ x, |Q.mass x - P.mass x| ≤ d) (f : Ω → ℝ) (hA : 0 ≤ A) (hf : ∀ x, |f x| ≤ A) :
    |Q.expect f - P.expect f| ≤ d * A := by
  unfold FiniteProbability.expect
  rw [← Finset.sum_sub_distrib]
  calc |∑ x, (Q.mass x * f x - P.mass x * f x)|
      ≤ ∑ x, |Q.mass x * f x - P.mass x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |Q.mass x - P.mass x| * A := by
        apply Finset.sum_le_sum
        intro x _
        rw [← sub_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)
    _ = (∑ x, |Q.mass x - P.mass x|) * A := by rw [Finset.sum_mul]
    _ ≤ d * A := mul_le_mul_of_nonneg_right hTV hA

theorem famDelta_le {Ω ι : Type*} [Fintype Ω] [Fintype ι] (P Q : FiniteProbability Ω) (d S : ℝ)
    (hTV : ∑ x, |Q.mass x - P.mass x| ≤ d) (H : ι → Ω → ℝ) (hS : 0 ≤ S)
    (hH : ∀ x, ∑ q, |H q x| ≤ S) :
    ∑ q, |Q.expect (H q) - P.expect (H q)| ≤ d * S := by
  unfold FiniteProbability.expect
  calc ∑ q, |∑ x, Q.mass x * H q x - ∑ x, P.mass x * H q x|
      ≤ ∑ q, ∑ x, |Q.mass x - P.mass x| * |H q x| := by
        apply Finset.sum_le_sum
        intro q _
        rw [← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        apply Finset.sum_congr rfl
        intro x _
        rw [← sub_mul, abs_mul]
    _ = ∑ x, |Q.mass x - P.mass x| * ∑ q, |H q x| := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
    _ ≤ ∑ x, |Q.mass x - P.mass x| * S := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left (hH x) (abs_nonneg _)
    _ = (∑ x, |Q.mass x - P.mass x|) * S := by rw [Finset.sum_mul]
    _ ≤ d * S := mul_le_mul_of_nonneg_right hTV hS

theorem absExpect_le {Ω : Type*} [Fintype Ω] (P : FiniteProbability Ω) (A : ℝ)
    (f : Ω → ℝ) (hf : ∀ x, |f x| ≤ A) : |P.expect f| ≤ A := by
  unfold FiniteProbability.expect
  calc |∑ x, P.mass x * f x| ≤ ∑ x, |P.mass x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, P.mass x * A := by
        apply Finset.sum_le_sum
        intro x _
        rw [abs_mul, abs_of_nonneg (P.mass_nonneg x)]
        exact mul_le_mul_of_nonneg_left (hf x) (P.mass_nonneg x)
    _ = A := by rw [← Finset.sum_mul, P.mass_sum, one_mul]

theorem famExpect_le {Ω ι : Type*} [Fintype Ω] [Fintype ι] (P : FiniteProbability Ω) (S : ℝ)
    (H : ι → Ω → ℝ) (hH : ∀ x, ∑ q, |H q x| ≤ S) :
    ∑ q, |P.expect (H q)| ≤ S := by
  unfold FiniteProbability.expect
  calc ∑ q, |∑ x, P.mass x * H q x| ≤ ∑ q, ∑ x, P.mass x * |H q x| := by
        apply Finset.sum_le_sum
        intro q _
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        apply Finset.sum_congr rfl
        intro x _
        rw [abs_mul, abs_of_nonneg (P.mass_nonneg x)]
    _ = ∑ x, P.mass x * ∑ q, |H q x| := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
    _ ≤ ∑ x, P.mass x * S := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left (hH x) (P.mass_nonneg x)
    _ = S := by rw [← Finset.sum_mul, P.mass_sum, one_mul]

theorem covRow_le {Ω ι : Type*} [Fintype Ω] [Fintype ι] (P Q : FiniteProbability Ω)
    (d A R : ℝ) (hd : 0 ≤ d) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hTV : ∑ x, |Q.mass x - P.mass x| ≤ d)
    (F : Ω → ℝ) (H : ι → Ω → ℝ)
    (hF : ∀ x, |F x| ≤ A) (hH : ∀ x, ∑ q, |H q x| ≤ R) :
    ∑ q, |Q.covariance F (H q) - P.covariance F (H q)| ≤ 3 * A * R * d := by
  have h1 := famDelta_le P Q d (A * R) hTV (fun q x => F x * H q x) (mul_nonneg hA hR) (by
    intro x
    simp only [abs_mul]
    rw [← Finset.mul_sum]
    exact mul_le_mul (hF x) (hH x) (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hA)
  have h2 := absDelta_le P Q d A hTV F hA hF
  have h3 := famExpect_le Q R H hH
  have h4 := absExpect_le P A F hF
  have h5 := famDelta_le P Q d R hTV H hR hH
  unfold FiniteProbability.covariance
  calc ∑ q, |(Q.expect (fun ω => F ω * H q ω) - Q.expect F * Q.expect (H q)) -
        (P.expect (fun ω => F ω * H q ω) - P.expect F * P.expect (H q))|
      ≤ ∑ q, (|Q.expect (fun ω => F ω * H q ω) - P.expect (fun ω => F ω * H q ω)| +
          |Q.expect F - P.expect F| * |Q.expect (H q)| +
          |P.expect F| * |Q.expect (H q) - P.expect (H q)|) := by
        apply Finset.sum_le_sum
        intro q _
        have e : (Q.expect (fun ω => F ω * H q ω) - Q.expect F * Q.expect (H q)) -
            (P.expect (fun ω => F ω * H q ω) - P.expect F * P.expect (H q)) =
            (Q.expect (fun ω => F ω * H q ω) - P.expect (fun ω => F ω * H q ω)) -
            (Q.expect F - P.expect F) * Q.expect (H q) -
            P.expect F * (Q.expect (H q) - P.expect (H q)) := by ring
        rw [e, ← abs_mul, ← abs_mul]
        exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ = ∑ q, |Q.expect (fun ω => F ω * H q ω) - P.expect (fun ω => F ω * H q ω)| +
          |Q.expect F - P.expect F| * ∑ q, |Q.expect (H q)| +
          |P.expect F| * ∑ q, |Q.expect (H q) - P.expect (H q)| := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ d * (A * R) + (d * A) * R + A * (d * R) := by
        refine add_le_add (add_le_add h1 (mul_le_mul h2 h3 (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity))) (mul_le_mul h4 h5 (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hA)
    _ = 3 * A * R * d := by ring

end Sol767


namespace Sol767

open Erdos390.Full

theorem tv_deleteGuards {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (μ : FiniteProbability Ω)
    (G : Finset Ω) (h : μ.guardMass G < 1) :
    ∑ x, |(μ.deleteGuards G h).mass x - μ.mass x| ≤ μ.guardPerturbation G := by
  set g := μ.guardMass G with hg
  have hg0 : 0 ≤ g := Finset.sum_nonneg (fun x _ => μ.mass_nonneg x)
  have h1g : 0 < 1 - g := sub_pos.mpr h
  have key : ∀ x, |(μ.deleteGuards G h).mass x - μ.mass x| =
      if x ∈ G then μ.mass x else μ.mass x * (g / (1 - g)) := by
    intro x
    by_cases hx : x ∈ G
    · rw [FiniteProbability.deleteGuards_mass_of_mem μ G h hx, if_pos hx, zero_sub, abs_neg,
        abs_of_nonneg (μ.mass_nonneg x)]
    · rw [FiniteProbability.deleteGuards_mass_of_not_mem μ G h hx, if_neg hx]
      have e : μ.mass x / (1 - μ.guardMass G) - μ.mass x = μ.mass x * (g / (1 - g)) := by
        rw [← hg]; field_simp; ring
      rw [e]
      exact abs_of_nonneg (mul_nonneg (μ.mass_nonneg x) (div_nonneg hg0 h1g.le))
  simp_rw [key]
  rw [Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sum_mul]
  have hc : ∑ x ∈ Finset.univ.filter (fun x => x ∉ G), μ.mass x = 1 - g := by
    rw [← μ.sum_mass_complement_guard G]
    congr 1
    ext x; simp
  rw [hc]
  unfold FiniteProbability.guardPerturbation
  rw [← hg]
  have : g + (1 - g) * (g / (1 - g)) = 2 * g := by field_simp; ring
  rw [show (∑ x ∈ G, μ.mass x) = g from rfl, this]
  rw [le_div_iff₀ h1g]
  nlinarith

theorem tv_sigma {C : Type*} [Fintype C] {Ω : C → Type*} [∀ c, Fintype (Ω c)]
    (w : FiniteProbability C) (μ ν : ∀ c, FiniteProbability (Ω c)) (d : ℝ)
    (h : ∀ c, ∑ x, |(ν c).mass x - (μ c).mass x| ≤ d) :
    ∑ x, |(FiniteProbability.sigmaMixture w ν).mass x - (FiniteProbability.sigmaMixture w μ).mass x|
      ≤ d := by
  rw [Fintype.sum_sigma]
  calc ∑ c, ∑ x, |(FiniteProbability.sigmaMixture w ν).mass ⟨c, x⟩ -
        (FiniteProbability.sigmaMixture w μ).mass ⟨c, x⟩|
      = ∑ c, w.mass c * ∑ x, |(ν c).mass x - (μ c).mass x| := by
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        show |w.mass c * (ν c).mass x - w.mass c * (μ c).mass x| = _
        rw [← mul_sub, abs_mul, abs_of_nonneg (w.mass_nonneg c)]
    _ ≤ ∑ c, w.mass c * d := by
        apply Finset.sum_le_sum
        intro c _
        exact mul_le_mul_of_nonneg_left (h c) (w.mass_nonneg c)
    _ = d := by rw [← Finset.sum_mul, w.mass_sum, one_mul]

open ArithmeticModel in
theorem sum_valuation_le {n W m M : ℕ} (hW : 1 < W) (hm : 0 < m) (hmM : m ≤ M) :
    ∑ q ∈ primeBand n W, valuation q m ≤ Real.log (M : ℝ) / Real.log (W : ℝ) := by
  have hlogW : 0 < Real.log (W : ℝ) := Real.log_pos (by exact_mod_cast hW)
  rw [le_div_iff₀ hlogW, Finset.sum_mul]
  have hstep : ∀ q ∈ primeBand n W, valuation q m * Real.log W ≤
      (m.factorization q : ℝ) * Real.log q := by
    intro q hq
    have hWq : W < q := cutoff_lt_of_mem_primeBand hq
    unfold valuation
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.log_le_log (by positivity) (by exact_mod_cast hWq.le)
  refine (Finset.sum_le_sum hstep).trans ?_
  have hsupp : ∑ q ∈ primeBand n W, (m.factorization q : ℝ) * Real.log q ≤
      ∑ q ∈ primeBand n W ∪ m.factorization.support, (m.factorization q : ℝ) * Real.log q := by
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    intro q _ _
    apply mul_nonneg (by positivity)
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · subst h0; simp
    · exact Real.log_nonneg (by exact_mod_cast h0)
  refine hsupp.trans ?_
  rw [← Finset.sum_subset Finset.subset_union_right (by
    intro q _ hq
    rw [Finsupp.notMem_support_iff] at hq
    simp [hq])]
  have hlog : Real.log (m : ℝ) = ∑ q ∈ m.factorization.support, (m.factorization q : ℝ) * Real.log q := by
    rw [Real.log_nat_eq_sum_factorization]
    rfl
  rw [← hlog]
  exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmM)

open ArithmeticModel in
theorem divInd_le_valuation {q m : ℕ} (hq : q.Prime) (hm : 0 < m) : divInd q m ≤ valuation q m := by
  unfold divInd valuation
  split_ifs with h
  · have := hq.factorization_pos_of_dvd hm.ne' h
    exact_mod_cast this
  · positivity

open ArithmeticModel in
theorem divInd_nonneg (q m : ℕ) : 0 ≤ divInd q m := by
  unfold divInd; split_ifs <;> norm_num

open ArithmeticModel in
theorem divInd_le_one (q m : ℕ) : divInd q m ≤ 1 := by
  unfold divInd; split_ifs <;> norm_num

end Sol767


namespace Sol767

open Erdos390.Full Erdos390.Full.PaperBridgeFit Erdos390.Full.PaperGuardCensus Erdos390.Full.ArithmeticModel Erdos390.Full.PrimePowerCovariance Erdos390.Full.ArithmeticBandGeometry

theorem ss {T : Finset ℕ} {F : Fintype {x // x ∈ T}} (φ : ℕ → ℝ) :
    (∑ x : {x // x ∈ T}, φ x.1) = ∑ k ∈ T, φ k :=
  (Finset.sum_subtype T (fun _ => Iff.rfl) φ).symm

theorem alg_id {S T Gd : Finset ℕ} (hT : T = S \ Gd) (hTn : T.Nonempty)
    {FT : Fintype {x // x ∈ T}} {FS : Fintype {x // x ∈ S}}
    (a f : ℕ → ℝ) (ha : ∀ k, 0 < a k) :
    ∑ x : {x // x ∈ T}, (1 / (T.card:ℝ) * a x.1 / ∑ y : {x // x ∈ T}, 1 / (T.card:ℝ) * a y.1) * f x.1 =
    ∑ x : {x // x ∈ S}, (if x.1 ∈ Gd then 0 else
        (1 / (S.card:ℝ) * a x.1 / ∑ y : {x // x ∈ S}, 1 / (S.card:ℝ) * a y.1) /
        (1 - ∑ ω ∈ GuardedUniformCell.guardSubtype S Gd,
          1 / (S.card:ℝ) * a ω.1 / ∑ y : {x // x ∈ S}, 1 / (S.card:ℝ) * a y.1)) * f x.1 := by
  have hSn : S.Nonempty := by
    obtain ⟨k, hk⟩ := hTn
    rw [hT] at hk
    exact ⟨k, (Finset.mem_sdiff.mp hk).1⟩
  rw [ss (F := FT) (fun k => (1 / (T.card:ℝ) * a k / ∑ y : {x // x ∈ T}, 1 / (T.card:ℝ) * a y.1) * f k)]
  rw [ss (F := FT) (fun k => 1 / (T.card:ℝ) * a k)]
  rw [ss (F := FS) (fun k => (if k ∈ Gd then 0 else
        (1 / (S.card:ℝ) * a k / ∑ y : {x // x ∈ S}, 1 / (S.card:ℝ) * a y.1) /
        (1 - ∑ ω ∈ GuardedUniformCell.guardSubtype S Gd,
          1 / (S.card:ℝ) * a ω.1 / ∑ y : {x // x ∈ S}, 1 / (S.card:ℝ) * a y.1)) * f k)]
  have hg : ∑ ω ∈ GuardedUniformCell.guardSubtype S Gd,
          1 / (S.card:ℝ) * a ω.1 / ∑ y : {x // x ∈ S}, 1 / (S.card:ℝ) * a y.1 =
      ∑ k ∈ S.filter (· ∈ Gd), 1 / (S.card:ℝ) * a k / ∑ y : {x // x ∈ S}, 1 / (S.card:ℝ) * a y.1 := by
    unfold GuardedUniformCell.guardSubtype
    rw [Finset.sum_filter, Finset.sum_filter]
    exact Finset.sum_subtype S (fun _ => Iff.rfl)
      (fun k => if k ∈ Gd then 1 / (S.card:ℝ) * a k / ∑ y : {x // x ∈ S}, 1 / (S.card:ℝ) * a y.1 else 0) |>.symm
  rw [hg, ss (F := FS) (fun k => 1 / (S.card:ℝ) * a k)]
  have hTc : (0:ℝ) < T.card := by exact_mod_cast hTn.card_pos
  have hSc : (0:ℝ) < S.card := by exact_mod_cast hSn.card_pos
  have hAT : 0 < ∑ k ∈ T, a k := Finset.sum_pos (fun k _ => ha k) hTn
  have hAS : 0 < ∑ k ∈ S, a k := Finset.sum_pos (fun k _ => ha k) hSn
  have hsplit : ∑ k ∈ S, a k = ∑ k ∈ S with k ∈ Gd, a k + ∑ k ∈ T, a k := by
    rw [hT, ← Finset.sum_filter_add_sum_filter_not S (· ∈ Gd)]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext k; simp
  have e1 : ∑ k ∈ T, 1 / (T.card:ℝ) * a k = 1 / (T.card:ℝ) * ∑ k ∈ T, a k := by
    rw [Finset.mul_sum]
  have e2 : ∑ k ∈ S, 1 / (S.card:ℝ) * a k = 1 / (S.card:ℝ) * ∑ k ∈ S, a k := by
    rw [Finset.mul_sum]
  rw [e1, e2]
  have e3 : ∑ k ∈ S with k ∈ Gd, 1 / (S.card:ℝ) * a k / (1 / (S.card:ℝ) * ∑ k ∈ S, a k) =
      (∑ k ∈ S with k ∈ Gd, a k) / ∑ k ∈ S, a k := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
    field_simp
  rw [e3]
  have h1 : 1 - (∑ k ∈ S with k ∈ Gd, a k) / ∑ k ∈ S, a k = (∑ k ∈ T, a k) / ∑ k ∈ S, a k := by
    field_simp
    linarith
  rw [h1]
  calc ∑ k ∈ T, (1 / (T.card:ℝ) * a k / (1 / (T.card:ℝ) * ∑ k ∈ T, a k)) * f k
      = ∑ k ∈ T, (a k / ∑ k ∈ T, a k) * f k := by
        apply Finset.sum_congr rfl
        intro k _
        field_simp
    _ = ∑ k ∈ S with k ∉ Gd, (a k / ∑ k ∈ T, a k) * f k := by
        rw [hT, Finset.sdiff_eq_filter]
    _ = ∑ k ∈ S, if k ∉ Gd then (a k / ∑ k ∈ T, a k) * f k else 0 := Finset.sum_filter _ _
    _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases h : k ∈ Gd
        · simp [h]
        · rw [if_neg h, if_pos h]
          field_simp
end Sol767


namespace Sol767

open Erdos390.Full Erdos390.Full.PaperBridgeFit Erdos390.Full.PaperGuardCensus Erdos390.Full.ArithmeticModel Erdos390.Full.PrimePowerCovariance Erdos390.Full.ArithmeticBandGeometry

theorem score_eq {Head Band : Type*} [Fintype Head] [DecidableEq Head] [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) [Nonempty Head] (xi : B.ParamSpace) (c : Cell Head)
    (m : B.sampleData.SampleAt c) :
    FiniteProbability.sigmaCellScore (B.scaledMediumScore xi) c m =
      ValuationScoreDomination.valuationScore (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L m.1 := by
  unfold FiniteProbability.sigmaCellScore BridgeData.scaledMediumScore
    ValuationScoreDomination.valuationScore
  rw [Finset.sum_subtype (primeBand B.sampleData.n B.sampleData.W) (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro q _
  rw [BridgeData.effectiveNatCoefficient_of_mem B xi q.2]
  rfl

theorem comp_id {Head Band : Type*} [Fintype Head] [DecidableEq Head] [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) [Nonempty Head] (P : Head → HeadPattern.Pattern)
    (I : PhysicalIntervals) {Cprom Cbank : ℕ}
    (G : Ledger B.sampleData.n Cprom Cbank)
    (hsep : physicalBound (I.upper .minus) B.sampleData.n <
      physicalBound (I.lower .plus) B.sampleData.n)
    (hrem : ∀ c : Cell Head, (rawCell P I B.sampleData.n c \ G.guards).Nonempty)
    (hEq : B.sampleData = canonicalSampleData (W := B.sampleData.W) P I G hsep hrem)
    (xi : B.ParamSpace)
    (hS : ∀ c : Cell Head, (rawCell P I B.sampleData.n c).Nonempty) (c : Cell Head)
    (hsmall : ((FiniteProbability.uniformOnFinset (rawCell P I B.sampleData.n c) (hS c)).exponentialTilt
        (fun m => ValuationScoreDomination.valuationScore (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L m.1)).guardMass
        (GuardedUniformCell.guardSubtype (rawCell P I B.sampleData.n c) G.guards) < 1)
    (f : ℕ → ℝ) :
    (B.cellMediumLaw xi c).expect (fun m => f m.1) =
      (((FiniteProbability.uniformOnFinset (rawCell P I B.sampleData.n c) (hS c)).exponentialTilt
        (fun m => ValuationScoreDomination.valuationScore (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L m.1)).deleteGuards
        (GuardedUniformCell.guardSubtype (rawCell P I B.sampleData.n c) G.guards) hsmall).expect
        (fun x => f x.1) := by
  have hcell : B.sampleData.cellFinset c = rawCell P I B.sampleData.n c \ G.guards :=
    congrArg (fun D => StructuredSampleData.cellFinset D c) hEq
  have hTn : (B.sampleData.cellFinset c).Nonempty := B.sampleData.cell_nonempty c
  simp only [FiniteProbability.expect, BridgeData.cellMediumLaw, FiniteProbability.exponentialTilt,
    FiniteProbability.expPartition, BridgeData.guardedCellProbability_mass, score_eq,
    FiniteProbability.deleteGuards, FiniteProbability.guardMass, FiniteProbability.uniformOnFinset_mass,
    GuardedUniformCell.mem_guardSubtype]
  exact alg_id hcell hTn (fun k => Real.exp (ValuationScoreDomination.valuationScore
    (primeBand B.sampleData.n B.sampleData.W) (B.effectiveNatCoefficient xi) B.L k)) f
    (fun k => Real.exp_pos _)

end Sol767



namespace Sol767

open Erdos390.Full Erdos390.Full.PaperBridgeFit Erdos390.Full.PaperGuardCensus Erdos390.Full.ArithmeticModel Erdos390.Full.PrimePowerCovariance Erdos390.Full.ArithmeticBandGeometry

theorem raw_bounds {Head : Type*} [Fintype Head] (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (n : ℕ) (c : Cell Head) {m : ℕ} (hm : m ∈ rawCell P I n c) :
    0 < m ∧ m ≤ physicalBound (I.upper c.2) n := by
  unfold rawCell at hm
  have h1 := (StructuredCells.mem_structuredCell.mp hm).1
  exact ⟨StructuredCells.pos_of_mem_smoothInterval h1, (StructuredCells.mem_smoothInterval.mp h1).2.1⟩

theorem sum_val_le_env {Head : Type*} [Fintype Head] (I : PhysicalIntervals) (n W : ℕ) (c : Cell Head)
    {m : ℕ} (hW : 1 < W) (hm0 : 0 < m) (hmle : m ≤ physicalBound (I.upper c.2) n) :
    ∑ q : BandPrime n W, valuation q.1 m ≤ valuationEnvelope I n W c := by
  unfold valuationEnvelope
  rw [← Finset.sum_subtype (primeBand n W) (fun _ => Iff.rfl) (fun q => valuation q m)]
  exact sum_valuation_le hW hm0 hmle

theorem valuation_nonneg' (q m : ℕ) : 0 ≤ valuation q m := by
  unfold valuation; positivity

/-- raw tilted component law on one unguarded cell -/
noncomputable def muC {Head Band : Type*} [Fintype Head] [DecidableEq Head] [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) [Nonempty Head] (P : Head → HeadPattern.Pattern)
    (I : PhysicalIntervals)
    (xi : B.ParamSpace) (hS : ∀ c : Cell Head, (rawCell P I B.sampleData.n c).Nonempty)
    (c : Cell Head) : FiniteProbability {x // x ∈ rawCell P I B.sampleData.n c} :=
  (FiniteProbability.uniformOnFinset (rawCell P I B.sampleData.n c) (hS c)).exponentialTilt
    (fun m => ValuationScoreDomination.valuationScore (primeBand B.sampleData.n B.sampleData.W)
      (B.effectiveNatCoefficient xi) B.L m.1)

noncomputable def wC {Head Band : Type*} [Fintype Head] [DecidableEq Head] [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) [Nonempty Head] (xi : B.ParamSpace) : FiniteProbability (Cell Head) :=
  FiniteProbability.tiltedSigmaWeight B.baselineCellProbability B.guardedCellProbability
    (B.scaledBridgeScore xi)

noncomputable def PL {Head Band : Type*} [Fintype Head] [DecidableEq Head] [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) [Nonempty Head] (P : Head → HeadPattern.Pattern)
    (I : PhysicalIntervals)
    (xi : B.ParamSpace) (hS : ∀ c : Cell Head, (rawCell P I B.sampleData.n c).Nonempty) :
    FiniteProbability (Σ c : Cell Head, {x // x ∈ rawCell P I B.sampleData.n c}) :=
  FiniteProbability.sigmaMixture (wC B xi) (muC B P I xi hS)

noncomputable def QL {Head Band : Type*} [Fintype Head] [DecidableEq Head] [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) [Nonempty Head] (P : Head → HeadPattern.Pattern)
    (I : PhysicalIntervals) {Cprom Cbank : ℕ}
    (G : Ledger B.sampleData.n Cprom Cbank)
    (xi : B.ParamSpace) (hS : ∀ c : Cell Head, (rawCell P I B.sampleData.n c).Nonempty)
    (hmass : ∀ c : Cell Head, (muC B P I xi hS c).guardMass
        (GuardedUniformCell.guardSubtype (rawCell P I B.sampleData.n c) G.guards) < 1) :
    FiniteProbability (Σ c : Cell Head, {x // x ∈ rawCell P I B.sampleData.n c}) :=
  FiniteProbability.sigmaMixture (wC B xi) (fun c => (muC B P I xi hS c).deleteGuards
    (GuardedUniformCell.guardSubtype (rawCell P I B.sampleData.n c) G.guards) (hmass c))

theorem rawCov {Head Band : Type*} [Fintype Head] [DecidableEq Head] [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) [Nonempty Head] (P : Head → HeadPattern.Pattern)
    (I : PhysicalIntervals) (Cmax : ℝ)
    (xi : B.ParamSpace) (hC_le : ∀ sigma, I.upper sigma ≤ Cmax)
    (hS : ∀ c : Cell Head, (rawCell P I B.sampleData.n c).Nonempty) (F H : ℕ → ℝ) :
    (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).probability.covariance
      (fun x => F ((B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).value x))
      (fun x => H ((B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).value x)) =
      (PL B P I xi hS).covariance (fun x => F x.2.1) (fun x => H x.2.1) := rfl

theorem guardExp {Head Band : Type*} [Fintype Head] [DecidableEq Head] [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) [Nonempty Head] (P : Head → HeadPattern.Pattern)
    (I : PhysicalIntervals) {Cprom Cbank : ℕ}
    (G : Ledger B.sampleData.n Cprom Cbank)
    (hsep : physicalBound (I.upper .minus) B.sampleData.n <
      physicalBound (I.lower .plus) B.sampleData.n)
    (hrem : ∀ c : Cell Head, (rawCell P I B.sampleData.n c \ G.guards).Nonempty)
    (hEq : B.sampleData = canonicalSampleData (W := B.sampleData.W) P I G hsep hrem)
    (xi : B.ParamSpace)
    (hS : ∀ c : Cell Head, (rawCell P I B.sampleData.n c).Nonempty)
    (hmass : ∀ c : Cell Head, (muC B P I xi hS c).guardMass
        (GuardedUniformCell.guardSubtype (rawCell P I B.sampleData.n c) G.guards) < 1)
    (F : ℕ → ℝ) :
    (B.canonicalGuardedMediumReferenceLaw xi).probability.expect (fun ω => F ω.2.1) =
      (QL B P I G xi hS hmass).expect (fun x => F x.2.1) := by
  show (FiniteProbability.sigmaMixture (wC B xi) (fun c => B.cellMediumLaw xi c)).expect _ = _
  unfold QL
  rw [FiniteProbability.sigmaMixture_expect, FiniteProbability.sigmaMixture_expect]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  exact comp_id B P I G hsep hrem hEq xi hS c (hmass c) F

theorem guardCov {Head Band : Type*} [Fintype Head] [DecidableEq Head] [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) [Nonempty Head] (P : Head → HeadPattern.Pattern)
    (I : PhysicalIntervals) {Cprom Cbank : ℕ}
    (G : Ledger B.sampleData.n Cprom Cbank)
    (hsep : physicalBound (I.upper .minus) B.sampleData.n <
      physicalBound (I.lower .plus) B.sampleData.n)
    (hrem : ∀ c : Cell Head, (rawCell P I B.sampleData.n c \ G.guards).Nonempty)
    (hEq : B.sampleData = canonicalSampleData (W := B.sampleData.W) P I G hsep hrem)
    (xi : B.ParamSpace)
    (hS : ∀ c : Cell Head, (rawCell P I B.sampleData.n c).Nonempty)
    (hmass : ∀ c : Cell Head, (muC B P I xi hS c).guardMass
        (GuardedUniformCell.guardSubtype (rawCell P I B.sampleData.n c) G.guards) < 1)
    (F H : ℕ → ℝ) :
    (B.canonicalGuardedMediumReferenceLaw xi).probability.covariance
      (fun x => F ((B.canonicalGuardedMediumReferenceLaw xi).value x))
      (fun x => H ((B.canonicalGuardedMediumReferenceLaw xi).value x)) =
      (QL B P I G xi hS hmass).covariance (fun x => F x.2.1) (fun x => H x.2.1) := by
  unfold FiniteProbability.covariance
  have h1 := guardExp B P I G hsep hrem hEq xi hS hmass F
  have h2 := guardExp B P I G hsep hrem hEq xi hS hmass H
  have h3 := guardExp B P I G hsep hrem hEq xi hS hmass (fun k => F k * H k)
  exact congrArg₂ (· - ·) h3 (congrArg₂ (· * ·) h1 h2)

theorem tvQP {Head Band : Type*} [Fintype Head] [DecidableEq Head] [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) [Nonempty Head] (P : Head → HeadPattern.Pattern)
    (I : PhysicalIntervals) {Cprom Cbank : ℕ}
    (G : Ledger B.sampleData.n Cprom Cbank)
    (xi : B.ParamSpace) (hS : ∀ c : Cell Head, (rawCell P I B.sampleData.n c).Nonempty)
    (hmass : ∀ c : Cell Head, (muC B P I xi hS c).guardMass
        (GuardedUniformCell.guardSubtype (rawCell P I B.sampleData.n c) G.guards) < 1)
    {d : ℝ}
    (hpert : ∀ c : Cell Head, (muC B P I xi hS c).guardPerturbation
        (GuardedUniformCell.guardSubtype (rawCell P I B.sampleData.n c) G.guards) ≤ d) :
    ∑ x, |(QL B P I G xi hS hmass).mass x - (PL B P I xi hS).mass x| ≤ d :=
  tv_sigma (wC B xi) (muC B P I xi hS) _ d
    (fun c => (tv_deleteGuards (muC B P I xi hS c) _ (hmass c)).trans (hpert c))

end Sol767



namespace Sol767

open Erdos390.Full Erdos390.Full.PaperBridgeFit Erdos390.Full.PaperGuardCensus Erdos390.Full.ArithmeticModel Erdos390.Full.PrimePowerCovariance Erdos390.Full.ArithmeticBandGeometry

theorem main
    {Head Band : Type*} [Fintype Head] [DecidableEq Head] [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) [Nonempty Head] (P : Head → HeadPattern.Pattern)
    (I : PhysicalIntervals) (Cmax : ℝ) {Cprom Cbank : ℕ}
    (G : Ledger B.sampleData.n Cprom Cbank)
    (hsep : physicalBound (I.upper .minus) B.sampleData.n <
      physicalBound (I.lower .plus) B.sampleData.n)
    (hrem : ∀ c : Cell Head, (rawCell P I B.sampleData.n c \ G.guards).Nonempty)
    (hEq : B.sampleData = canonicalSampleData (W := B.sampleData.W) P I G hsep hrem)
    (xi : B.ParamSpace) (hC_le : ∀ sigma, I.upper sigma ≤ Cmax)
    (hS : ∀ c : Cell Head, (rawCell P I B.sampleData.n c).Nonempty)
    (hW : 1 < B.sampleData.W) {K d : ℝ} (hK : 0 ≤ K) (hd : 0 ≤ d)
    (henv : ∀ c : Cell Head, valuationEnvelope I B.sampleData.n B.sampleData.W c ≤ K)
    (hmass : ∀ c : Cell Head, ((FiniteProbability.uniformOnFinset (rawCell P I B.sampleData.n c) (hS c)).exponentialTilt
        (fun m => ValuationScoreDomination.valuationScore (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L m.1)).guardMass
        (GuardedUniformCell.guardSubtype (rawCell P I B.sampleData.n c) G.guards) < 1)
    (hpert : ∀ c : Cell Head, ((FiniteProbability.uniformOnFinset (rawCell P I B.sampleData.n c) (hS c)).exponentialTilt
        (fun m => ValuationScoreDomination.valuationScore (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L m.1)).guardPerturbation
        (GuardedUniformCell.guardSubtype (rawCell P I B.sampleData.n c) G.guards) ≤ d)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    ∑ q : BandPrime B.sampleData.n B.sampleData.W,
      |((B.canonicalGuardedMediumReferenceLaw xi).covVV p.1 q.1 -
          (B.canonicalGuardedMediumReferenceLaw xi).covII p.1 q.1) -
        ((B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covVV p.1 q.1 -
          (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covII p.1 q.1)| ≤
      guardPowerCorrectionRowError K d
 := by
  have hRsum : ∀ x : (Σ c : Cell Head, {x // x ∈ rawCell P I B.sampleData.n c}),
      ∑ q : BandPrime B.sampleData.n B.sampleData.W, |valuation q.1 x.2.1| ≤ K := by
    intro x
    obtain ⟨h0, hle⟩ := raw_bounds P I B.sampleData.n x.1 x.2.2
    simp only [abs_of_nonneg (valuation_nonneg' _ _)]
    exact (sum_val_le_env I B.sampleData.n B.sampleData.W x.1 hW h0 hle).trans (henv x.1)
  have hIsum : ∀ x : (Σ c : Cell Head, {x // x ∈ rawCell P I B.sampleData.n c}),
      ∑ q : BandPrime B.sampleData.n B.sampleData.W, |divInd q.1 x.2.1| ≤ K := by
    intro x
    obtain ⟨h0, hle⟩ := raw_bounds P I B.sampleData.n x.1 x.2.2
    refine le_trans ?_ ((sum_val_le_env I B.sampleData.n B.sampleData.W x.1 hW h0 hle).trans (henv x.1))
    apply Finset.sum_le_sum
    intro q _
    rw [abs_of_nonneg (divInd_nonneg _ _)]
    exact divInd_le_valuation (prime_of_mem_primeBand q.2) h0
  have hVp : ∀ x : (Σ c : Cell Head, {x // x ∈ rawCell P I B.sampleData.n c}),
      |valuation p.1 x.2.1| ≤ K := by
    intro x
    refine le_trans ?_ (hRsum x)
    exact Finset.single_le_sum (f := fun q : BandPrime B.sampleData.n B.sampleData.W => |valuation q.1 x.2.1|)
      (fun q _ => abs_nonneg _) (Finset.mem_univ p)
  have hIp : ∀ x : (Σ c : Cell Head, {x // x ∈ rawCell P I B.sampleData.n c}),
      |divInd p.1 x.2.1| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (divInd_nonneg _ _)]
    exact divInd_le_one _ _
  have hTV := tvQP B P I G xi hS hmass hpert
  have hVV := covRow_le (Ω := (Σ c : Cell Head, {x // x ∈ rawCell P I B.sampleData.n c})) (ι := BandPrime B.sampleData.n B.sampleData.W) (PL B P I xi hS) (QL B P I G xi hS hmass) d K K hd hK hK hTV
    (fun x => valuation p.1 x.2.1) (fun q x => valuation q.1 x.2.1) hVp hRsum
  have hII := covRow_le (Ω := (Σ c : Cell Head, {x // x ∈ rawCell P I B.sampleData.n c})) (ι := BandPrime B.sampleData.n B.sampleData.W) (PL B P I xi hS) (QL B P I G xi hS hmass) d 1 K hd zero_le_one hK hTV
    (fun x => divInd p.1 x.2.1) (fun q x => divInd q.1 x.2.1) hIp hIsum
  have hsplit : ∀ q : BandPrime B.sampleData.n B.sampleData.W,
      |((B.canonicalGuardedMediumReferenceLaw xi).covVV p.1 q.1 -
          (B.canonicalGuardedMediumReferenceLaw xi).covII p.1 q.1) -
        ((B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covVV p.1 q.1 -
          (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covII p.1 q.1)| ≤
      |(QL B P I G xi hS hmass).covariance (fun x => valuation p.1 x.2.1) (fun x => valuation q.1 x.2.1) -
          (PL B P I xi hS).covariance (fun x => valuation p.1 x.2.1) (fun x => valuation q.1 x.2.1)| +
      |(QL B P I G xi hS hmass).covariance (fun x => divInd p.1 x.2.1) (fun x => divInd q.1 x.2.1) -
          (PL B P I xi hS).covariance (fun x => divInd p.1 x.2.1) (fun x => divInd q.1 x.2.1)| := by
    intro q
    have a1 := guardCov B P I G hsep hrem hEq xi hS hmass (valuation p.1) (valuation q.1)
    have a2 := guardCov B P I G hsep hrem hEq xi hS hmass (divInd p.1) (divInd q.1)
    have a3 := rawCov B P I Cmax xi hC_le hS (valuation p.1) (valuation q.1)
    have a4 := rawCov B P I Cmax xi hC_le hS (divInd p.1) (divInd q.1)
    unfold BoundedValuationLaw.covVV BoundedValuationLaw.covII BoundedValuationLaw.V BoundedValuationLaw.I
    rw [a1, a2, a3, a4]
    have e : ∀ a b c e : ℝ, (a - b) - (c - e) = (a - c) - (b - e) := by intros; ring
    rw [e]
    exact abs_sub _ _
  calc _ ≤ ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (|(QL B P I G xi hS hmass).covariance (fun x => valuation p.1 x.2.1) (fun x => valuation q.1 x.2.1) -
            (PL B P I xi hS).covariance (fun x => valuation p.1 x.2.1) (fun x => valuation q.1 x.2.1)| +
          |(QL B P I G xi hS hmass).covariance (fun x => divInd p.1 x.2.1) (fun x => divInd q.1 x.2.1) -
            (PL B P I xi hS).covariance (fun x => divInd p.1 x.2.1) (fun x => divInd q.1 x.2.1)|) :=
        Finset.sum_le_sum (fun q _ => hsplit q)
    _ ≤ 3 * K * K * d + 3 * 1 * K * d := by
        rw [Finset.sum_add_distrib]
        exact add_le_add hVV hII
    _ ≤ guardPowerCorrectionRowError K d := by
        unfold guardPowerCorrectionRowError
        have : 0 ≤ 2 * ((K + K * d) * (K * d) + K * (K * d)) + 2 * ((1 + d) * (K * d) + K * d) := by
          positivity
        nlinarith

end Sol767


set_option maxHeartbeats 4000000 in
open BigOperators in
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : @Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3)
  [inst_4 : Nonempty.{u_1 + 1} Head] (P : Head → Erdos390.Full.HeadPattern.Pattern)
  (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (Cmax : Real) {Cprom Cbank : Nat}
  (G :
    Erdos390.Full.PaperGuardCensus.Ledger
      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B))
      Cprom Cbank)
  (hsep :
    @LT.lt.{0} Nat instLTNat
      (Erdos390.Full.ArithmeticModel.physicalBound (I.upper Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B)))
      (Erdos390.Full.ArithmeticModel.physicalBound (I.lower Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B))))
  (hremaining :
    ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
      @Finset.Nonempty.{0} Nat
        (@SDiff.sdiff.{0} (Finset.{0} Nat) (@Finset.instSDiff.{0} Nat instDecidableEqNat)
          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B))
            c)
          (@Erdos390.Full.PaperGuardCensus.Ledger.guards
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B))
            Cprom Cbank G))),
  @Eq.{u_1 + 1} (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head inst)
      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B)
      (@Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Head inst P I
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B))
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B))
        Cprom Cbank G hsep hremaining) →
    ∀ (xi : @Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B)
      (hC_le : ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), @LE.le.{0} Real Real.instLE (I.upper sigma) Cmax),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B)) →
        ∀ {K d : Real},
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) d →
              (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                  @LE.le.{0} Real Real.instLE
                    (@Erdos390.Full.PaperGuardCensus.valuationEnvelope.{u_1} Head inst I
                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                          inst_3 B))
                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                          inst_3 B))
                      c)
                    K) →
                (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                    @LT.lt.{0} Real Real.instLT
                      (@Erdos390.Full.FiniteProbability.guardMass.{0}
                        (@Subtype.{1} Nat fun (x : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                            (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              c)
                            x)
                        (@Finset.Subtype.fintype.{0} Nat
                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))
                            c))
                        (@Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                          (@Subtype.{1} Nat fun (x : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                              (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                c)
                              x)
                          (@Finset.Subtype.fintype.{0} Nat
                            (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              c))
                          (@Erdos390.Full.FiniteProbability.uniformOnFinset.{0} Nat
                            (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              c)
                            (@Finset.Nonempty.mono.{0} Nat
                              (@SDiff.sdiff.{0} (Finset.{0} Nat) (@Finset.instSDiff.{0} Nat instDecidableEqNat)
                                (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  c)
                                (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  Cprom Cbank G))
                              (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                c)
                              (@Finset.sdiff_subset.{0} Nat instDecidableEqNat
                                (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  c)
                                (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  Cprom Cbank G))
                              (hremaining c)))
                          fun
                            (m :
                              @Subtype.{1} Nat fun (x : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                  (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    c)
                                  x) =>
                          Erdos390.Full.ValuationScoreDomination.valuationScore
                            (Erdos390.Full.ArithmeticModel.primeBand
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B)))
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.effectiveNatCoefficient.{u_1, u_2} Head Band inst
                              inst_1 inst_2 inst_3 B xi)
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3
                              B)
                            (@Subtype.val.{1} Nat
                              (fun (x : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                  (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    c)
                                  x)
                              m))
                        (@Erdos390.Full.GuardedUniformCell.guardSubtype.{0} Nat instDecidableEqNat
                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))
                            c)
                          (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))
                            Cprom Cbank G)))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                  (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                      @LE.le.{0} Real Real.instLE
                        (@Erdos390.Full.FiniteProbability.guardPerturbation.{0}
                          (@Subtype.{1} Nat fun (x : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                              (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                c)
                              x)
                          (@Finset.Subtype.fintype.{0} Nat
                            (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              c))
                          (@Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                            (@Subtype.{1} Nat fun (x : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  c)
                                x)
                            (@Finset.Subtype.fintype.{0} Nat
                              (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                c))
                            (@Erdos390.Full.FiniteProbability.uniformOnFinset.{0} Nat
                              (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                c)
                              (@Finset.Nonempty.mono.{0} Nat
                                (@SDiff.sdiff.{0} (Finset.{0} Nat) (@Finset.instSDiff.{0} Nat instDecidableEqNat)
                                  (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    c)
                                  (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    Cprom Cbank G))
                                (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  c)
                                (@Finset.sdiff_subset.{0} Nat instDecidableEqNat
                                  (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    c)
                                  (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    Cprom Cbank G))
                                (hremaining c)))
                            fun
                              (m :
                                @Subtype.{1} Nat fun (x : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                          inst_1 inst_2 inst_3 B))
                                      c)
                                    x) =>
                            Erdos390.Full.ValuationScoreDomination.valuationScore
                              (Erdos390.Full.ArithmeticModel.primeBand
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B)))
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.effectiveNatCoefficient.{u_1, u_2} Head Band
                                inst inst_1 inst_2 inst_3 B xi)
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3
                                B)
                              (@Subtype.val.{1} Nat
                                (fun (x : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                          inst_1 inst_2 inst_3 B))
                                      c)
                                    x)
                                m))
                          (@Erdos390.Full.GuardedUniformCell.guardSubtype.{0} Nat instDecidableEqNat
                            (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              c)
                            (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              Cprom Cbank G)))
                        d) →
                    ∀
                      (p :
                        Erdos390.Full.ArithmeticBandGeometry.BandPrime
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                              inst_3 B))
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                              inst_3 B))),
                      @LE.le.{0} Real Real.instLE
                        (@Finset.sum.{0, 0}
                          (Erdos390.Full.ArithmeticBandGeometry.BandPrime
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B)))
                          Real Real.instAddCommMonoid
                          (@Finset.univ.{0}
                            (Erdos390.Full.ArithmeticBandGeometry.BandPrime
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B)))
                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.instFintypeBandPrime
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))))
                          fun
                            (q :
                              Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))) =>
                          @abs.{0} Real Real.lattice Real.instAddGroup
                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                (@Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1}
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleFintype.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleEndpoint.{u_1, u_2} Head Band inst
                                    inst_1 inst_2 inst_3 B)
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.canonicalGuardedMediumReferenceLaw.{u_1,
                                        u_2}
                                    Head Band inst inst_1 inst_2 inst_3 B inst_4 xi)
                                  (@Subtype.val.{1} Nat
                                    (fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (Erdos390.Full.ArithmeticModel.primeBand
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B)))
                                        p)
                                    p)
                                  (@Subtype.val.{1} Nat
                                    (fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (Erdos390.Full.ArithmeticModel.primeBand
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B)))
                                        p)
                                    q))
                                (@Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleFintype.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleEndpoint.{u_1, u_2} Head Band inst
                                    inst_1 inst_2 inst_3 B)
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.canonicalGuardedMediumReferenceLaw.{u_1,
                                        u_2}
                                    Head Band inst inst_1 inst_2 inst_3 B inst_4 xi)
                                  (@Subtype.val.{1} Nat
                                    (fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (Erdos390.Full.ArithmeticModel.primeBand
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B)))
                                        p)
                                    p)
                                  (@Subtype.val.{1} Nat
                                    (fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (Erdos390.Full.ArithmeticModel.primeBand
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B)))
                                        p)
                                    q)))
                              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                (@Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1}
                                  (@Sigma.{u_1, 0} (Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head)
                                    fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                    @Subtype.{1} Nat fun (x : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          c)
                                        x)
                                  (@Sigma.instFintype.{u_1, 0} (Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head)
                                    (fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                      @Subtype.{1} Nat fun (x : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            c)
                                          x)
                                    (fun (i : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                      @Finset.Subtype.fintype.{0} Nat
                                        (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          i))
                                    (@instFintypeProd.{u_1, 0} Head Erdos390.Full.PaperBridgeFit.PhysicalSign inst
                                      Erdos390.Full.PaperBridgeFit.instFintypePhysicalSign))
                                  (Erdos390.Full.ArithmeticModel.physicalBound Cmax
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B)))
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.canonicalRawMediumReferenceLaw.{u_1, u_2}
                                    Head Band inst inst_1 inst_2 inst_3 B inst_4 P I Cmax xi hC_le
                                    fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                    @Finset.Nonempty.mono.{0} Nat
                                      (@SDiff.sdiff.{0} (Finset.{0} Nat) (@Finset.instSDiff.{0} Nat instDecidableEqNat)
                                        (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          c)
                                        (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          Cprom Cbank G))
                                      (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        c)
                                      (@Finset.sdiff_subset.{0} Nat instDecidableEqNat
                                        (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          c)
                                        (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          Cprom Cbank G))
                                      (hremaining c))
                                  (@Subtype.val.{1} Nat
                                    (fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (Erdos390.Full.ArithmeticModel.primeBand
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B)))
                                        p)
                                    p)
                                  (@Subtype.val.{1} Nat
                                    (fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (Erdos390.Full.ArithmeticModel.primeBand
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B)))
                                        p)
                                    q))
                                (@Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                                  (@Sigma.{u_1, 0} (Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head)
                                    fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                    @Subtype.{1} Nat fun (x : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          c)
                                        x)
                                  (@Sigma.instFintype.{u_1, 0} (Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head)
                                    (fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                      @Subtype.{1} Nat fun (x : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            c)
                                          x)
                                    (fun (i : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                      @Finset.Subtype.fintype.{0} Nat
                                        (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          i))
                                    (@instFintypeProd.{u_1, 0} Head Erdos390.Full.PaperBridgeFit.PhysicalSign inst
                                      Erdos390.Full.PaperBridgeFit.instFintypePhysicalSign))
                                  (Erdos390.Full.ArithmeticModel.physicalBound Cmax
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B)))
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.canonicalRawMediumReferenceLaw.{u_1, u_2}
                                    Head Band inst inst_1 inst_2 inst_3 B inst_4 P I Cmax xi hC_le
                                    fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                    @Finset.Nonempty.mono.{0} Nat
                                      (@SDiff.sdiff.{0} (Finset.{0} Nat) (@Finset.instSDiff.{0} Nat instDecidableEqNat)
                                        (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          c)
                                        (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          Cprom Cbank G))
                                      (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        c)
                                      (@Finset.sdiff_subset.{0} Nat instDecidableEqNat
                                        (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          c)
                                        (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          Cprom Cbank G))
                                      (hremaining c))
                                  (@Subtype.val.{1} Nat
                                    (fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (Erdos390.Full.ArithmeticModel.primeBand
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B)))
                                        p)
                                    p)
                                  (@Subtype.val.{1} Nat
                                    (fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (Erdos390.Full.ArithmeticModel.primeBand
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B)))
                                        p)
                                    q)))))
                        (Erdos390.Full.PaperGuardCensus.guardPowerCorrectionRowError K d) := by
  intro Head Band inst inst_1 inst_2 inst_3 B inst_4 P I Cmax Cprom Cbank G hsep hremaining hEq xi hC_le hW K d hK hd henv hmass hpert p
  exact Sol767.main B P I Cmax G hsep hremaining hEq xi hC_le
    (fun c => Finset.Nonempty.mono Finset.sdiff_subset (hremaining c)) hW hK hd henv hmass hpert p
