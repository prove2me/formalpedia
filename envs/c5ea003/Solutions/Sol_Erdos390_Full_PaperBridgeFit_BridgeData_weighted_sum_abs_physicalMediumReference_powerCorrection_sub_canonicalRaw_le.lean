-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.weighted_sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T12:29:05.674301+00:00
-- url     : https://prove2.me/submissions/7d271806-3f49-4b8a-aa2c-bfdf317535c8

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Definitions.Def_erdos390_analytic_foundations_001
import Definitions.Def_erdos390_analytic_foundations_002
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

namespace RhoPos

open Erdos390.Full.DickmanBasic

theorem rA_succ (n : ℕ) (x : ℝ) : rhoApprox (n + 1) x =
    if x ≤ 1 then 1 else 1 - ∫ t in (1 : ℝ)..x, rhoApprox n (t - 1) / safeDenom t := rfl

theorem rA_le_one (n : ℕ) (x : ℝ) (hx : x ≤ 1) : rhoApprox n x = 1 := by
  cases n with
  | zero => rfl
  | succ n => rw [rA_succ, if_pos hx]

theorem rA_agree : ∀ n : ℕ, ∀ x : ℝ, x ≤ (n : ℝ) + 1 → rhoApprox (n + 1) x = rhoApprox n x
  | 0, x, hx => by
    rw [rA_succ, if_pos (by simpa using hx)]; rfl
  | n + 1, x, hx => by
    rw [rA_succ, rA_succ n]
    split_ifs with h1
    · rfl
    · congr 1
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith : (1:ℝ) ≤ x)] at ht
      simp only
      rw [rA_agree n (t - 1) (by push_cast at hx; linarith [ht.2])]

theorem safeDenom_cont : Continuous safeDenom := continuous_id.max continuous_const

theorem safeDenom_pos (t : ℝ) : 0 < safeDenom t := lt_of_lt_of_le one_pos (le_max_right _ _)

theorem rA_cont : ∀ n : ℕ, Continuous (rhoApprox n)
  | 0 => continuous_const
  | n + 1 => by
    have hg : Continuous (fun t => rhoApprox n (t - 1) / safeDenom t) :=
      ((rA_cont n).comp (continuous_id.sub continuous_const)).div safeDenom_cont
        (fun t => (safeDenom_pos t).ne')
    have hP : Continuous (fun x => ∫ t in (1 : ℝ)..x, rhoApprox n (t - 1) / safeDenom t) :=
      intervalIntegral.continuous_primitive (fun a b => hg.intervalIntegrable a b) 1
    have : rhoApprox (n + 1) = fun x =>
        if x ≤ 1 then 1 else 1 - ∫ t in (1 : ℝ)..x, rhoApprox n (t - 1) / safeDenom t := rfl
    rw [this]
    refine Continuous.if_le continuous_const (continuous_const.sub hP) continuous_id continuous_const ?_
    intro x hx
    rw [hx, intervalIntegral.integral_same, sub_zero]

/-- the integrand of the fifth stage -/
noncomputable def g4 (t : ℝ) : ℝ := rhoApprox 4 (t - 1) / safeDenom t

theorem g4_cont : Continuous g4 :=
  ((rA_cont 4).comp (continuous_id.sub continuous_const)).div safeDenom_cont
    (fun t => (safeDenom_pos t).ne')

theorem r5_eq (x : ℝ) (hx : 1 ≤ x) : rho x = 1 - ∫ t in (1 : ℝ)..x, g4 t := by
  show rhoApprox 5 x = _
  rw [rA_succ]
  split_ifs with h
  · have : x = 1 := le_antisymm h hx
    rw [this, intervalIntegral.integral_same, sub_zero]
  · rfl

theorem r4_eq_r5 (s : ℝ) (hs : s ≤ 5) : rhoApprox 4 s = rho s := by
  show rhoApprox 4 s = rhoApprox 5 s
  rw [rA_agree 4 s (by norm_num; linarith)]

theorem rho_cont : Continuous rho := rA_cont 5

theorem g4_eq (t : ℝ) (ht : 1 ≤ t) (ht6 : t ≤ 6) : t * g4 t = rho (t - 1) := by
  unfold g4 safeDenom
  rw [max_eq_left ht, r4_eq_r5 _ (by linarith)]
  field_simp

theorem identity (x : ℝ) (hx1 : 1 ≤ x) (hx6 : x ≤ 6) :
    x * rho x = ∫ t in (x - 1)..x, rho t := by
  set Φ : ℝ → ℝ := fun y => ∫ t in (1 : ℝ)..y, g4 t with hΦ
  set Ψ : ℝ → ℝ := fun y => ∫ t in (0 : ℝ)..y, rho t with hΨ
  set H : ℝ → ℝ := fun y => y * (1 - Φ y) - (Ψ y - Ψ (y - 1)) with hH
  have dΦ : ∀ y, HasDerivAt Φ (g4 y) y := fun y => g4_cont.integral_hasStrictDerivAt 1 y |>.hasDerivAt
  have dΨ : ∀ y, HasDerivAt Ψ (rho y) y := fun y => rho_cont.integral_hasStrictDerivAt 0 y |>.hasDerivAt
  have dH : ∀ y, HasDerivAt H ((1 * (1 - Φ y) + y * (0 - g4 y)) - (rho y - rho (y - 1) * 1)) y := by
    intro y
    have h1 := (hasDerivAt_id y).mul ((hasDerivAt_const y (1:ℝ)).sub (dΦ y))
    have h2 := (dΨ y).sub ((dΨ (y - 1)).comp y ((hasDerivAt_id y).sub_const 1))
    exact h1.sub h2
  have hcont : Continuous H := by
    have cΦ : Continuous Φ := continuous_iff_continuousAt.mpr fun y => (dΦ y).continuousAt
    have cΨ : Continuous Ψ := continuous_iff_continuousAt.mpr fun y => (dΨ y).continuousAt
    exact (continuous_id.mul (continuous_const.sub cΦ)).sub (cΨ.sub (cΨ.comp (continuous_id.sub continuous_const)))
  have hconst := constant_of_has_deriv_right_zero hcont.continuousOn (a := 1) (b := 6)
    (fun y hy => by
      have e : (1 * (1 - Φ y) + y * (0 - g4 y)) - (rho y - rho (y - 1) * 1) = 0 := by
        have a1 : 1 - Φ y = rho y := (r5_eq y hy.1).symm
        have a2 : y * g4 y = rho (y - 1) := g4_eq y hy.1 hy.2.le
        rw [a1]
        linear_combination (-1 : ℝ) * a2
      rw [← e]
      exact (dH y).hasDerivWithinAt) x ⟨hx1, hx6⟩
  have H1 : H 1 = 0 := by
    simp only [hH, hΦ, hΨ, intervalIntegral.integral_same, sub_zero, sub_self, mul_one]
    have : ∫ t in (0:ℝ)..1, rho t = ∫ t in (0:ℝ)..1, (1:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      exact rA_le_one 5 t ht.2
    rw [this]
    simp
  rw [H1] at hconst
  have hx : x * (1 - Φ x) = Ψ x - Ψ (x - 1) := by
    have := hconst; simp only [hH] at this; linarith
  have hr : rho x = 1 - Φ x := r5_eq x hx1
  rw [hr, hx]
  simp only [hΨ]
  rw [intervalIntegral.integral_interval_sub_left (rho_cont.intervalIntegrable _ _) (rho_cont.intervalIntegrable _ _)]


theorem rho_nonneg_step (a x : ℝ) (ha : 1 ≤ a) (hax : a ≤ x) (hx : x ≤ a + 1 / 2) (hx6 : x ≤ 6)
    (hpos : ∀ y, 0 ≤ y → y ≤ a → 0 < rho y) : 0 < rho x := by
  have hRx : rho x = rho a - ∫ t in a..x, g4 t := by
    rw [r5_eq x (by linarith), r5_eq a ha]
    rw [← intervalIntegral.integral_interval_sub_left (g4_cont.intervalIntegrable 1 x)
      (g4_cont.intervalIntegrable 1 a)]
    ring
  have hI : ∫ t in a..x, g4 t ≤ ∫ t in a..x, rho (t - 1) / a := by
    apply intervalIntegral.integral_mono_on hax (g4_cont.intervalIntegrable _ _)
      ((rho_cont.comp (continuous_id.sub continuous_const)).div_const a |>.intervalIntegrable _ _)
    intro t ht
    have ht1 : 1 ≤ t := by linarith [ht.1]
    have hgt : g4 t = rho (t - 1) / t := by
      rw [eq_div_iff (by linarith), mul_comm]; exact g4_eq t ht1 (by linarith [ht.2])
    rw [hgt]
    have h0 : 0 ≤ rho (t - 1) := (hpos (t - 1) (by linarith [ht.1]) (by linarith [ht.2])).le
    exact div_le_div_of_nonneg_left h0 (by linarith) ht.1
  have hsub : ∫ t in a..x, rho (t - 1) / a = (∫ t in (a - 1)..(x - 1), rho t) / a := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_right (fun t => rho t)]
  have hid := identity a ha (by linarith)
  have hsplit : (∫ t in (a - 1)..a, rho t) - ∫ t in (a - 1)..(x - 1), rho t =
      ∫ t in (x - 1)..a, rho t := by
    rw [intervalIntegral.integral_interval_sub_left (rho_cont.intervalIntegrable _ _)
      (rho_cont.intervalIntegrable _ _)]
  have hposI : 0 < ∫ t in (x - 1)..a, rho t := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (rho_cont.intervalIntegrable _ _)
    · intro y hy
      exact hpos y (by linarith [hy.1]) hy.2.le
    · linarith
  have ha0 : 0 < a := by linarith
  rw [hRx]
  have : rho a = (∫ t in (a - 1)..a, rho t) / a := by
    rw [eq_div_iff ha0.ne', mul_comm]; exact hid
  rw [this]
  have : (∫ t in (a - 1)..a, rho t) / a - (∫ t in (a - 1)..(x - 1), rho t) / a =
      (∫ t in (x - 1)..a, rho t) / a := by rw [← sub_div, hsplit]
  have hle : (∫ t in (a - 1)..a, rho t) / a - (∫ t in (a - 1)..(x - 1), rho t) / a ≤
      (∫ t in (a - 1)..a, rho t) / a - ∫ t in a..x, g4 t := by
    rw [← hsub]; linarith
  linarith [div_pos hposI ha0]

theorem rho_pos_up (a : ℝ) (ha : 1 ≤ a) (ha6 : a + 1 / 2 ≤ 6)
    (hpos : ∀ y, 0 ≤ y → y ≤ a → 0 < rho y) : ∀ y, 0 ≤ y → y ≤ a + 1 / 2 → 0 < rho y := by
  intro y hy0 hy
  rcases le_or_gt y a with h | h
  · exact hpos y hy0 h
  · exact rho_nonneg_step a y ha h.le hy (by linarith) hpos

theorem rho_U_pos : 0 < rho U := by
  have h1 : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → 0 < rho y := by
    intro y _ hy; rw [show rho y = rhoApprox 5 y from rfl, rA_le_one 5 y hy]; exact one_pos
  have h2 := rho_pos_up 1 (by norm_num) (by norm_num) h1
  have h3 := rho_pos_up (1 + 1/2) (by norm_num) (by norm_num) h2
  have h4 := rho_pos_up (1 + 1/2 + 1/2) (by norm_num) (by norm_num) h3
  have h5 := rho_pos_up (1 + 1/2 + 1/2 + 1/2) (by norm_num) (by norm_num) h4
  have h6 := rho_pos_up (1 + 1/2 + 1/2 + 1/2 + 1/2) (by norm_num) (by norm_num) h5
  have h7 := rho_pos_up (1 + 1/2 + 1/2 + 1/2 + 1/2 + 1/2) (by norm_num) (by norm_num) h6
  have h8 := rho_pos_up (1 + 1/2 + 1/2 + 1/2 + 1/2 + 1/2 + 1/2) (by norm_num) (by norm_num) h7
  exact h8 U (by unfold U; norm_num) (by unfold U; norm_num)

end RhoPos

namespace SolC77

open Erdos390.Full Erdos390.Full.PaperBridgeFit Erdos390.Full.PaperGuardCensus Erdos390.Full.ArithmeticModel Erdos390.Full.ArithmeticBandGeometry

theorem tilt_mass_le {α : Type*} (S : Finset α) (hS : S.Nonempty) (s : S → ℝ) (K : ℝ)
    (hK : ∀ x, |s x| ≤ K) (x : S) :
    ((FiniteProbability.uniformOnFinset S hS).exponentialTilt s).mass x ≤ Real.exp (2 * K) / S.card := by
  have hc : (0:ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hZ : Real.exp (-K) ≤ (FiniteProbability.uniformOnFinset S hS).expPartition s := by
    unfold FiniteProbability.expPartition FiniteProbability.expect
    simp only [FiniteProbability.uniformOnFinset_mass]
    calc Real.exp (-K) = ∑ _ω : S, 1 / (S.card:ℝ) * Real.exp (-K) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
          field_simp
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro ω _
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.exp_le_exp.mpr
          have := hK ω
          linarith [neg_abs_le (s ω)]
  have hZpos : 0 < Real.exp (-K) := Real.exp_pos _
  show 1 / (S.card:ℝ) * Real.exp (s x) / (FiniteProbability.uniformOnFinset S hS).expPartition s ≤ _
  rw [div_le_div_iff₀ (lt_of_lt_of_le hZpos hZ) hc]
  have h1 : Real.exp (s x) ≤ Real.exp K := Real.exp_le_exp.mpr (le_trans (le_abs_self _) (hK x))
  have h2 : Real.exp (2 * K) = Real.exp K * Real.exp K := by rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp K * Real.exp (-K) = 1 := by rw [← Real.exp_add]; simp
  have hEK : 0 < Real.exp K := Real.exp_pos _
  calc 1 / (S.card:ℝ) * Real.exp (s x) * S.card = Real.exp (s x) := by field_simp
    _ ≤ Real.exp K := h1
    _ = Real.exp K * Real.exp K * Real.exp (-K) := by rw [mul_assoc, h3, mul_one]
    _ ≤ Real.exp (2 * K) * (FiniteProbability.uniformOnFinset S hS).expPartition s := by
        rw [h2]; exact mul_le_mul_of_nonneg_left hZ (by positivity)

theorem guardMass_le {α : Type*} [DecidableEq α] (S G : Finset α) (hS : S.Nonempty) (s : S → ℝ) (K : ℝ)
    (hK : ∀ x, |s x| ≤ K) :
    ((FiniteProbability.uniformOnFinset S hS).exponentialTilt s).guardMass
      (GuardedUniformCell.guardSubtype S G) ≤ Real.exp (2 * K) * G.card / S.card := by
  unfold FiniteProbability.guardMass
  have hcard : (GuardedUniformCell.guardSubtype S G).card ≤ G.card := by
    apply Finset.card_le_card_of_injOn (fun x : S => x.1)
    · intro x hx
      simpa using (GuardedUniformCell.mem_guardSubtype.mp hx)
    · intro x _ y _ h
      exact Subtype.ext h
  calc ∑ x ∈ GuardedUniformCell.guardSubtype S G,
        ((FiniteProbability.uniformOnFinset S hS).exponentialTilt s).mass x
      ≤ ∑ _x ∈ GuardedUniformCell.guardSubtype S G, Real.exp (2 * K) / S.card :=
        Finset.sum_le_sum (fun x _ => tilt_mass_le S hS s K hK x)
    _ = (GuardedUniformCell.guardSubtype S G).card * (Real.exp (2 * K) / S.card) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ G.card * (Real.exp (2 * K) / S.card) := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = Real.exp (2 * K) * G.card / S.card := by ring

theorem pert_le (g : ℝ) (h0 : 0 ≤ g) (h : g ≤ 1 / 2) : 2 * g / (1 - g) ≤ 4 * g := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem census_le {n Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank) :
    (G.guards.card : ℝ) ≤ ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (Scale.L n + 2)) * y n := by
  have h1 : G.guards.card ≤ Cprom * yNat n + Cbank * yNat n * scaleSlots n * 3 := by
    rw [← card_guardSlot]
    unfold Ledger.guards
    exact Finset.card_image_le.trans (by rw [Finset.card_univ])
  have hy0 : 0 ≤ y n := by unfold y; positivity
  have hL0 : 0 ≤ Scale.L n := by unfold Scale.L; exact Real.log_natCast_nonneg n
  have hyN : (yNat n : ℝ) ≤ y n := Nat.floor_le hy0
  have hsS : (scaleSlots n : ℝ) ≤ Scale.L n + 2 := by
    unfold scaleSlots
    push_cast
    have := Nat.ceil_lt_add_one hL0
    linarith
  calc (G.guards.card : ℝ) ≤ ((Cprom * yNat n + Cbank * yNat n * scaleSlots n * 3 : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ = (Cprom : ℝ) * yNat n + 3 * (Cbank : ℝ) * scaleSlots n * yNat n := by push_cast; ring
    _ ≤ (Cprom : ℝ) * y n + 3 * (Cbank : ℝ) * (Scale.L n + 2) * y n := by
        have hc1 : (0:ℝ) ≤ Cprom := Nat.cast_nonneg _
        have hc2 : (0:ℝ) ≤ Cbank := Nat.cast_nonneg _
        have hs0 : (0:ℝ) ≤ scaleSlots n := Nat.cast_nonneg _
        have hyN0 : (0:ℝ) ≤ yNat n := Nat.cast_nonneg _
        have a1 : (Cprom : ℝ) * yNat n ≤ Cprom * y n := mul_le_mul_of_nonneg_left hyN hc1
        have a2 : 3 * (Cbank : ℝ) * scaleSlots n * yNat n ≤ 3 * (Cbank : ℝ) * (Scale.L n + 2) * y n := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hsS (by positivity)) hyN hyN0 (by positivity)
        linarith
    _ = _ := by ring

theorem headDensity_pos (P : HeadPattern.Pattern) : 0 < PaperScaleMarkedCell.headDensity P := by
  unfold PaperScaleMarkedCell.headDensity
  have hf : 0 < P.factor := by
    unfold HeadPattern.Pattern.factor
    exact Finset.prod_pos (fun p hp => pow_pos (P.prime_mem p hp).pos _)
  have hm : 0 < P.modulus := by
    unfold HeadPattern.Pattern.modulus
    exact Finset.prod_pos (fun p hp => (P.prime_mem p hp).pos)
  have ht : 0 < P.modulus.totient := Nat.totient_pos.mpr hm
  have : (0:ℝ) < P.factor := by exact_mod_cast hf
  have : (0:ℝ) < P.modulus := by exact_mod_cast hm
  have : (0:ℝ) < P.modulus.totient := by exact_mod_cast ht
  positivity

theorem density_pos (P : HeadPattern.Pattern) (A B : ℝ) (hAB : A < B) :
    0 < PaperScaleMarkedCell.paperCellDensity P A B := by
  unfold PaperScaleMarkedCell.paperCellDensity
  have := headDensity_pos P
  have := RhoPos.rho_U_pos
  have : 0 < B - A := by linarith
  positivity

end SolC77

namespace SolC77

open Erdos390.Full Erdos390.Full.PaperBridgeFit Erdos390.Full.PaperGuardCensus Erdos390.Full.ArithmeticModel Erdos390.Full.ArithmeticBandGeometry

theorem arith (g E Gc S dens n cr D : ℝ) (hg : g ≤ E * Gc / S) (hE : 0 < E) (hGc : 0 ≤ Gc)
    (hdens : dens * n / 2 ≤ S) (hd : 0 < dens) (hn : 0 < n) (h3 : Gc / n ≤ cr) (hD : 8 * E / dens ≤ D)
    (hcr : 0 ≤ cr) : 4 * g ≤ D * cr := by
  have hlow : 0 < dens * n / 2 := by positivity
  have h2 : E * Gc / S ≤ E * Gc / (dens * n / 2) :=
    div_le_div_of_nonneg_left (by positivity) hlow hdens
  have h4 : 4 * (E * Gc / (dens * n / 2)) = (8 * E / dens) * (Gc / n) := by
    field_simp
    ring
  have h8 : 0 ≤ 8 * E / dens := by positivity
  calc 4 * g ≤ 4 * (E * Gc / (dens * n / 2)) := by linarith
    _ = (8 * E / dens) * (Gc / n) := h4
    _ ≤ (8 * E / dens) * cr := mul_le_mul_of_nonneg_left h3 h8
    _ ≤ D * cr := mul_le_mul_of_nonneg_right hD hcr

theorem main2
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
    (hW : 1 < B.sampleData.W) {Kscore Cenv : ℝ} (hCenv : 0 ≤ Cenv)
    (hscore : ∀ (c : Cell Head) (m : {x // x ∈ rawCell P I B.sampleData.n c}),
      |ValuationScoreDomination.valuationScore (primeBand B.sampleData.n B.sampleData.W)
        (B.effectiveNatCoefficient xi) B.L m.1| ≤ Kscore)
    (hguard : ∀ c : Cell Head, Real.exp (2 * Kscore) * (G.guards.card : ℝ) /
      ((rawCell P I B.sampleData.n c).card : ℝ) ≤ 1 / 2)
    (hdens : ∀ c : Cell Head, PaperScaleMarkedCell.paperCellDensity (P c.1) (I.lower c.2) (I.upper c.2) *
      (B.sampleData.n : ℝ) / 2 ≤ ((rawCell P I B.sampleData.n c).card : ℝ))
    (henv : ∀ c : Cell Head, valuationEnvelope I B.sampleData.n B.sampleData.W c ≤
      Cenv * Scale.L B.sampleData.n)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    (p.1 : ℝ) * ∑ q : BandPrime B.sampleData.n B.sampleData.W,
      |((B.canonicalGuardedMediumReferenceLaw xi).covVV p.1 q.1 -
          (B.canonicalGuardedMediumReferenceLaw xi).covII p.1 q.1) -
        ((B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covVV p.1 q.1 -
          (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covII p.1 q.1)| ≤
      BridgeData.guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv
        (BridgeData.canonicalGuardPerturbationConstant P I Kscore) B.sampleData.n := by
  have hn : 0 < B.sampleData.n := by
    obtain ⟨h⟩ := ‹Nonempty Head›
    obtain ⟨m, hm⟩ := hS (h, PhysicalSign.plus)
    obtain ⟨h0, hle⟩ := Sol767.raw_bounds P I B.sampleData.n _ hm
    rcases Nat.eq_zero_or_pos B.sampleData.n with h0n | h0n
    · rw [h0n] at hle
      simp [physicalBound] at hle
      omega
    · exact h0n
  have hnR : (0:ℝ) < B.sampleData.n := by exact_mod_cast hn
  have hmass_le : ∀ c : Cell Head,
      ((FiniteProbability.uniformOnFinset (rawCell P I B.sampleData.n c) (hS c)).exponentialTilt
        (fun m => ValuationScoreDomination.valuationScore (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L m.1)).guardMass
        (GuardedUniformCell.guardSubtype (rawCell P I B.sampleData.n c) G.guards) ≤
      Real.exp (2 * Kscore) * (G.guards.card : ℝ) / ((rawCell P I B.sampleData.n c).card : ℝ) :=
    fun c => guardMass_le (rawCell P I B.sampleData.n c) G.guards (hS c) _ Kscore (hscore c)
  have hmass : ∀ c : Cell Head,
      ((FiniteProbability.uniformOnFinset (rawCell P I B.sampleData.n c) (hS c)).exponentialTilt
        (fun m => ValuationScoreDomination.valuationScore (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L m.1)).guardMass
        (GuardedUniformCell.guardSubtype (rawCell P I B.sampleData.n c) G.guards) < 1 :=
    fun c => lt_of_le_of_lt ((hmass_le c).trans (hguard c)) (by norm_num)
  have hy0 : 0 ≤ y B.sampleData.n := by unfold y; positivity
  have hL0 : 0 ≤ Scale.L B.sampleData.n := by unfold Scale.L; exact Real.log_natCast_nonneg _
  have hcr0 : 0 ≤ censusRatioMajorant Cprom Cbank B.sampleData.n := by
    unfold censusRatioMajorant
    apply div_nonneg _ hnR.le
    apply mul_nonneg _ hy0
    positivity
  have hterm0 : ∀ c : Cell Head, 0 ≤ 8 * Real.exp (2 * Kscore) /
      PaperScaleMarkedCell.paperCellDensity (P c.1) (I.lower c.2) (I.upper c.2) := by
    intro c
    have := density_pos (P c.1) (I.lower c.2) (I.upper c.2) (I.lower_lt_upper c.2)
    positivity
  have hD : ∀ c : Cell Head, 8 * Real.exp (2 * Kscore) /
      PaperScaleMarkedCell.paperCellDensity (P c.1) (I.lower c.2) (I.upper c.2) ≤
      BridgeData.canonicalGuardPerturbationConstant P I Kscore := by
    intro c
    unfold BridgeData.canonicalGuardPerturbationConstant
    exact Finset.single_le_sum (f := fun c : Cell Head => 8 * Real.exp (2 * Kscore) /
      PaperScaleMarkedCell.paperCellDensity (P c.1) (I.lower c.2) (I.upper c.2))
      (fun c _ => hterm0 c) (Finset.mem_univ c)
  have hD0 : 0 ≤ BridgeData.canonicalGuardPerturbationConstant P I Kscore := by
    unfold BridgeData.canonicalGuardPerturbationConstant
    exact Finset.sum_nonneg (fun c _ => hterm0 c)
  have hpert : ∀ c : Cell Head,
      ((FiniteProbability.uniformOnFinset (rawCell P I B.sampleData.n c) (hS c)).exponentialTilt
        (fun m => ValuationScoreDomination.valuationScore (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L m.1)).guardPerturbation
        (GuardedUniformCell.guardSubtype (rawCell P I B.sampleData.n c) G.guards) ≤
      BridgeData.canonicalGuardPerturbationConstant P I Kscore *
        censusRatioMajorant Cprom Cbank B.sampleData.n := by
    intro c
    have hg0 : 0 ≤ ((FiniteProbability.uniformOnFinset (rawCell P I B.sampleData.n c) (hS c)).exponentialTilt
        (fun m => ValuationScoreDomination.valuationScore (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L m.1)).guardMass
        (GuardedUniformCell.guardSubtype (rawCell P I B.sampleData.n c) G.guards) :=
      Finset.sum_nonneg (fun x _ => FiniteProbability.mass_nonneg _ x)
    have hhalf := (hmass_le c).trans (hguard c)
    unfold FiniteProbability.guardPerturbation
    refine (pert_le _ hg0 hhalf).trans ?_
    have hdpos := density_pos (P c.1) (I.lower c.2) (I.upper c.2) (I.lower_lt_upper c.2)
    have h3 : (G.guards.card : ℝ) / (B.sampleData.n : ℝ) ≤ censusRatioMajorant Cprom Cbank B.sampleData.n := by
      unfold censusRatioMajorant
      exact div_le_div_of_nonneg_right (census_le G) hnR.le
    exact arith _ _ _ _ _ _ _ _ (hmass_le c) (Real.exp_pos _) (Nat.cast_nonneg _) (hdens c) hdpos hnR h3
      (hD c) hcr0
  have hK0 : 0 ≤ Cenv * Scale.L B.sampleData.n := mul_nonneg hCenv hL0
  have hd0 : 0 ≤ BridgeData.canonicalGuardPerturbationConstant P I Kscore *
      censusRatioMajorant Cprom Cbank B.sampleData.n := mul_nonneg hD0 hcr0
  have hmain := Sol767.main B P I Cmax G hsep hrem hEq xi hC_le hS hW hK0 hd0 henv hmass hpert p
  unfold BridgeData.guardPowerCorrectionWeightedMajorant
  have hp : (p.1 : ℝ) ≤ (yNat B.sampleData.n : ℝ) := by
    have h := p.2
    unfold primeBand at h
    rw [Finset.mem_filter, Nat.mem_primesBelow] at h
    exact_mod_cast Nat.lt_succ_iff.mp h.1.1
  have hrow0 : 0 ≤ guardPowerCorrectionRowError (Cenv * Scale.L B.sampleData.n)
      (BridgeData.canonicalGuardPerturbationConstant P I Kscore *
        censusRatioMajorant Cprom Cbank B.sampleData.n) := by
    unfold guardPowerCorrectionRowError
    positivity
  exact (mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_right hp hrow0)

end SolC77


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
        ∀ {Kscore Cenv : Real},
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Cenv →
            (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head)
                (m :
                  @Subtype.{1} Nat fun (x : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                      (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                            inst_3 B))
                        c)
                      x),
                @LE.le.{0} Real Real.instLE
                  (@abs.{0} Real Real.lattice Real.instAddGroup
                    (Erdos390.Full.ValuationScoreDomination.valuationScore
                      (Erdos390.Full.ArithmeticModel.primeBand
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                            inst_3 B))
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                            inst_3 B)))
                      (@Erdos390.Full.PaperBridgeFit.BridgeData.effectiveNatCoefficient.{u_1, u_2} Head Band inst inst_1
                        inst_2 inst_3 B xi)
                      (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B)
                      (@Subtype.val.{1} Nat
                        (fun (x : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                            (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              c)
                            x)
                        m)))
                  Kscore) →
              (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                  @LE.le.{0} Real Real.instLE
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (Real.exp
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            Kscore))
                        (@Nat.cast.{0} Real Real.instNatCast
                          (@Finset.card.{0} Nat
                            (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              Cprom Cbank G))))
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@Finset.card.{0} Nat
                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))
                            c))))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) →
                (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                    @LE.le.{0} Real Real.instLE
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (Erdos390.Full.PaperScaleMarkedCell.paperCellDensity
                            (P (@Prod.fst.{u_1, 0} Head Erdos390.Full.PaperBridgeFit.PhysicalSign c))
                            (I.lower (@Prod.snd.{u_1, 0} Head Erdos390.Full.PaperBridgeFit.PhysicalSign c))
                            (I.upper (@Prod.snd.{u_1, 0} Head Erdos390.Full.PaperBridgeFit.PhysicalSign c)))
                          (@Nat.cast.{0} Real Real.instNatCast
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))))
                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@Finset.card.{0} Nat
                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))
                            c)))) →
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
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Cenv
                          (Erdos390.Full.Scale.L
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))))) →
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
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@Nat.cast.{0} Real Real.instNatCast
                            (@Subtype.val.{1} Nat
                              (fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                  (Erdos390.Full.ArithmeticModel.primeBand
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B)))
                                  p)
                              p))
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
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))) =>
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
                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                  Band inst inst_1 inst_2 inst_3 B))
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
                                        (@SDiff.sdiff.{0} (Finset.{0} Nat)
                                          (@Finset.instSDiff.{0} Nat instDecidableEqNat)
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
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
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
                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                  Band inst inst_1 inst_2 inst_3 B))
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
                                        (@SDiff.sdiff.{0} (Finset.{0} Nat)
                                          (@Finset.instSDiff.{0} Nat instDecidableEqNat)
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
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
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
                                      q))))))
                        (Erdos390.Full.PaperBridgeFit.BridgeData.guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.canonicalGuardPerturbationConstant.{u_1} Head inst P
                            I Kscore)
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                              inst_3 B))) := by
  intro Head Band inst inst_1 inst_2 inst_3 B inst_4 P I Cmax Cprom Cbank G hsep hremaining hEq xi hC_le hW Kscore Cenv hCenv hscore hguard hdens henv p
  exact SolC77.main2 B P I Cmax G hsep hremaining hEq xi hC_le
    (fun c => Finset.Nonempty.mono Finset.sdiff_subset (hremaining c)) hW hCenv hscore hguard hdens henv p
