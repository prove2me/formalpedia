-- Prove2me | solution 1 for BanditAlgorithm.posterior_diagonal_representation
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T04:29:30.036796+00:00
-- url     : https://prove2.me/submissions/18392377-eca0-42c6-b6d3-da14ac2e5c7c

import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Theorems.Thm_InformationTheory_finite_range_mutualInformation_ne_top
import Theorems.Thm_InformationTheory_klDiv_compProd_self_eq_lintegral_of_ae
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal BigOperators

namespace BanditAlgorithm

private theorem posterior_observation_kernel_eq_compProd
    {k : ℕ} {X : Type*} [MeasurableSpace X]
    (Sx : Measure X) [IsProbabilityMeasure Sx]
    (q : Measure (Fin k)) [IsProbabilityMeasure q]
    (reward : Fin k → X → Set.Icc (0 : ℝ) 1)
    (hreward : ∀ a, Measurable (reward a)) :
    let obs := fun z : X × Fin k ↦ (z.2, reward z.2 z.1)
    let Pab : Kernel (Fin k) (Set.Icc (0 : ℝ) 1) :=
      Kernel.ofFunOfCountable (fun b ↦ Measure.map (reward b) Sx)
    Measure.map obs (Sx.prod q) = q ⊗ₘ Pab := by
  dsimp only
  let obs := fun z : X × Fin k ↦ (z.2, reward z.2 z.1)
  let Pab : Kernel (Fin k) (Set.Icc (0 : ℝ) 1) :=
    Kernel.ofFunOfCountable (fun b ↦ Measure.map (reward b) Sx)
  letI : IsMarkovKernel Pab := ⟨fun b ↦ by
    dsimp [Pab]
    exact Measure.isProbabilityMeasure_map (hreward b).aemeasurable⟩
  apply Measure.ext_prod
  intro s u hs hu
  have hobs : Measurable obs := by
    apply measurable_from_prod_countable_left
    intro b
    exact measurable_const.prodMk (hreward b)
  rw [Measure.map_apply hobs (hs.prod hu), Measure.compProd_apply_prod hs hu]
  let S : Finset (Fin k) := s.toFinite.toFinset
  have hS : (S : Set (Fin k)) = s := Set.Finite.coe_toFinset s.toFinite
  have hpre : obs ⁻¹' (s ×ˢ u) =
      ⋃ b ∈ S, (reward b ⁻¹' u) ×ˢ ({b} : Set (Fin k)) := by
    ext z
    simpa [obs, ← hS, and_comm]
  rw [hpre, measure_biUnion_finset]
  swap
  · intro b hb c hc hbc
    apply Set.disjoint_left.2
    intro z hzb hzc
    have hb' : z.2 = b := by simpa using hzb.2
    have hc' : z.2 = c := by simpa using hzc.2
    exact hbc (hb'.symm.trans hc')
  swap
  · intro b hb
    exact (hu.preimage (hreward b)).prod (MeasurableSet.singleton b)
  simp_rw [Measure.prod_prod]
  rw [← hS, MeasureTheory.lintegral_finset]
  apply Finset.sum_congr rfl
  intro b hb
  rw [show Pab b u = Sx (reward b ⁻¹' u) by
    change Measure.map (reward b) Sx u = _
    rw [Measure.map_apply (hreward b) hu]]

private theorem posterior_independent_product_disintegration
    {k : ℕ} {X : Type*} [MeasurableSpace X]
    (R : Measure X) [IsProbabilityMeasure R]
    (q : Measure (Fin k)) [IsProbabilityMeasure q]
    (opt : X → Fin k) (hopt : Measurable opt)
    (K : Kernel (Fin k) X) [IsMarkovKernel K]
    (hdis : q ⊗ₘ K = Measure.map (fun x ↦ (opt x, x)) R) :
    let Kq := K.prod (Kernel.const (Fin k) q)
    Measure.map (fun z : X × Fin k ↦ (opt z.1, (z.1, z.2))) (R.prod q) =
      q ⊗ₘ Kq := by
  dsimp only
  let Kq := K.prod (Kernel.const (Fin k) q)
  apply Measure.ext_prod₃
  intro s u v hs hu hv
  have hf : Measurable (fun z : X × Fin k ↦ (opt z.1, (z.1, z.2))) :=
    (hopt.comp measurable_fst).prodMk (measurable_fst.prodMk measurable_snd)
  rw [Measure.map_apply hf (hs.prod (hu.prod hv))]
  have hpre :
      (fun z : X × Fin k ↦ (opt z.1, (z.1, z.2))) ⁻¹'
          (s ×ˢ (u ×ˢ v)) = (opt ⁻¹' s ∩ u) ×ˢ v := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff]
    aesop
  rw [hpre, Measure.prod_prod, Measure.compProd_apply_prod hs (hu.prod hv)]
  simp_rw [Kernel.prod_apply, Kernel.const_apply]
  change R (opt ⁻¹' s ∩ u) * q v =
    ∫⁻ a in s, (K a).prod q (u ×ˢ v) ∂q
  simp_rw [Measure.prod_prod]
  rw [MeasureTheory.lintegral_mul_const (q v) (Kernel.measurable_coe K hu)]
  have hrect := congrArg (fun m : Measure (Fin k × X) ↦ m (s ×ˢ u)) hdis
  change (q ⊗ₘ K) (s ×ˢ u) =
    Measure.map (fun x ↦ (opt x, x)) R (s ×ˢ u) at hrect
  have hpair : Measurable (fun x ↦ (opt x, x)) := hopt.prodMk measurable_id
  rw [Measure.compProd_apply_prod hs hu,
    Measure.map_apply hpair (hs.prod hu)] at hrect
  have hpre2 : (fun x ↦ (opt x, x)) ⁻¹' (s ×ˢ u) = opt ⁻¹' s ∩ u := by
    ext x
    simp
  rw [hpre2] at hrect
  rw [hrect]

theorem _root_.solution
    {k : ℕ} [NeZero k]
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (R : Measure X) [IsProbabilityMeasure R]
    (opt : X → Fin k) (hopt : Measurable opt)
    (reward : Fin k → X → Set.Icc (0 : ℝ) 1)
    (hreward : ∀ a, Measurable (reward a)) :
    let q := Measure.map opt R
    let rho := R.prod q
    let obs := fun z : X × Fin k ↦ (z.2, reward z.2 z.1)
    ∃ (p : Fin k → ℝ)
      (P M : Fin k → Measure (Set.Icc (0 : ℝ) 1)),
      (∀ a, IsProbabilityMeasure (P a)) ∧
      (∀ a, IsProbabilityMeasure (M a)) ∧
      (∀ a, klDiv (P a) (M a) ≠ ∞) ∧
      (∫ z, ((reward (opt z.1) z.1).1 - (reward z.2 z.1).1) ∂rho) =
        ∑ a, p a * ((∫ z, z.1 ∂P a) - ∫ z, z.1 ∂M a) ∧
      (∑ a, p a ^ 2 * (klDiv (P a) (M a)).toReal) ≤
        (klDiv (Measure.map (fun z ↦ (opt z.1, obs z)) rho)
          (q.prod (Measure.map obs rho))).toReal := by
  dsimp only
  let q := Measure.map opt R
  let rho := R.prod q
  let K := condDistrib id opt R
  let Kq := K.prod (Kernel.const (Fin k) q)
  let obs := fun z : X × Fin k ↦ (z.2, reward z.2 z.1)
  let L := Kq.map obs
  let Mker : Kernel (Fin k) (Set.Icc (0 : ℝ) 1) :=
    Kernel.ofFunOfCountable (fun b ↦ Measure.map (reward b) R)
  let Praw : Fin k → Fin k → Measure (Set.Icc (0 : ℝ) 1) :=
    fun a b ↦ Measure.map (reward b) (K a)
  let p : Fin k → ℝ := fun a ↦ q.real {a}
  let M : Fin k → Measure (Set.Icc (0 : ℝ) 1) := fun a ↦ Mker a
  let P : Fin k → Measure (Set.Icc (0 : ℝ) 1) := fun a ↦
    if q {a} = 0 then M a else Praw a a
  have hobs : Measurable obs := by
    apply measurable_from_prod_countable_left
    intro b
    exact measurable_const.prodMk (hreward b)
  letI : IsProbabilityMeasure q := by
    dsimp [q]
    exact Measure.isProbabilityMeasure_map hopt.aemeasurable
  letI : IsProbabilityMeasure rho := by dsimp [rho]; infer_instance
  letI : IsMarkovKernel K := by dsimp [K]; infer_instance
  letI : IsMarkovKernel Kq := by dsimp [Kq]; infer_instance
  letI : IsMarkovKernel L := by
    dsimp [L]
    exact Kernel.IsMarkovKernel.map Kq hobs
  letI : IsMarkovKernel Mker := ⟨fun b ↦ by
    dsimp [Mker]
    exact Measure.isProbabilityMeasure_map (hreward b).aemeasurable⟩
  have hMprob : ∀ a, IsProbabilityMeasure (M a) := fun a ↦ by
    dsimp [M]
    infer_instance
  have hPrawprob : ∀ a b, IsProbabilityMeasure (Praw a b) := fun a b ↦ by
    dsimp [Praw]
    exact Measure.isProbabilityMeasure_map (hreward b).aemeasurable
  have hPprob : ∀ a, IsProbabilityMeasure (P a) := fun a ↦ by
    dsimp [P]
    split <;> infer_instance
  have hdis : q ⊗ₘ K = Measure.map (fun x ↦ (opt x, x)) R := by
    dsimp [q, K]
    exact compProd_map_condDistrib aemeasurable_id
  have hprod : Measure.map (fun z : X × Fin k ↦ (opt z.1, (z.1, z.2))) rho =
      q ⊗ₘ Kq := by
    exact posterior_independent_product_disintegration R q opt hopt K hdis
  have hobsM : Measure.map obs rho = q ⊗ₘ Mker := by
    dsimp [rho, Mker]
    exact posterior_observation_kernel_eq_compProd R q reward hreward
  have hjoint : Measure.map (fun z ↦ (opt z.1, obs z)) rho = q ⊗ₘ L := by
    calc
      Measure.map (fun z ↦ (opt z.1, obs z)) rho =
          Measure.map (Prod.map id obs)
            (Measure.map (fun z : X × Fin k ↦ (opt z.1, (z.1, z.2))) rho) := by
        symm
        have hg : Measurable (fun z : X × Fin k ↦ (opt z.1, (z.1, z.2))) :=
          (hopt.comp measurable_fst).prodMk (measurable_fst.prodMk measurable_snd)
        rw [Measure.map_map (measurable_id.prodMap hobs) hg]
        rfl
      _ = Measure.map (Prod.map id obs) (q ⊗ₘ Kq) := by rw [hprod]
      _ = q ⊗ₘ L := by
        rw [Measure.compProd_map hobs]
  let Pker : Fin k → Kernel (Fin k) (Set.Icc (0 : ℝ) 1) := fun a ↦
    Kernel.ofFunOfCountable (fun b ↦ Praw a b)
  letI : ∀ a, IsMarkovKernel (Pker a) := fun a ↦ ⟨fun b ↦ hPrawprob a b⟩
  have hKcomp : K ∘ₘ q = R := by
    calc
      K ∘ₘ q = (q ⊗ₘ K).snd := by rw [Measure.snd_compProd]
      _ = (Measure.map (fun x ↦ (opt x, x)) R).snd := by rw [hdis]
      _ = R := by simpa using (Measure.snd_map_prodMk (Y := id) hopt)
  have hmix (b : Fin k) : (K.map (reward b)) ∘ₘ q = M b := by
    calc
      (K.map (reward b)) ∘ₘ q = (K ∘ₘ q).map (reward b) := by
        exact (Measure.map_comp q K (hreward b)).symm
      _ = R.map (reward b) := by rw [hKcomp]
      _ = M b := by rfl
  have hacP : ∀ᵐ a ∂q, ∀ᵐ b ∂q, Praw a b ≪ M b := by
    rw [ae_iff_of_countable]
    intro a ha
    rw [ae_iff_of_countable]
    intro b hb
    have hab := Measure.absolutelyContinuous_comp_of_countable
      (μ := q) (κ := K.map (reward b))
    rw [hmix b, ae_iff_of_countable] at hab
    have hab' := hab a ha
    rw [Kernel.map_apply K (hreward b) a] at hab'
    exact hab'
  have hL (a : Fin k) : L a = q ⊗ₘ Pker a := by
    rw [show L a = Measure.map obs ((K a).prod q) by
      dsimp [L, Kq]
      rw [Kernel.map_apply _ hobs]
      simp_rw [Kernel.prod_apply, Kernel.const_apply]]
    exact posterior_observation_kernel_eq_compProd (K a) q reward hreward
  have hacL : ∀ᵐ a ∂q, L a ≪ Measure.map obs rho := by
    filter_upwards [hacP] with a ha
    rw [hL a, hobsM]
    exact Measure.AbsolutelyContinuous.compProd_right ha
  have hinfoEq :
      klDiv (Measure.map (fun z ↦ (opt z.1, obs z)) rho)
          (q.prod (Measure.map obs rho)) =
        ∫⁻ a, klDiv (L a) (Measure.map obs rho) ∂q := by
    rw [hjoint, ← Measure.compProd_const]
    exact InformationTheory.klDiv_compProd_self_eq_lintegral_of_ae
      q L (Kernel.const (Fin k) (Measure.map obs rho)) (by simpa using hacL)
  have hlocalEq : ∀ᵐ a ∂q,
      klDiv (L a) (Measure.map obs rho) =
        ∫⁻ b, klDiv (Praw a b) (M b) ∂q := by
    filter_upwards [hacP] with a ha
    rw [hL a, hobsM]
    simpa [Pker, M] using
      (InformationTheory.klDiv_compProd_self_eq_lintegral_of_ae
        q (Pker a) Mker ha)
  have hdoubleEq :
      klDiv (Measure.map (fun z ↦ (opt z.1, obs z)) rho)
          (q.prod (Measure.map obs rho)) =
        ∫⁻ a, ∫⁻ b, klDiv (Praw a b) (M b) ∂q ∂q := by
    rw [hinfoEq]
    exact MeasureTheory.lintegral_congr_ae hlocalEq
  have hinfoFinite :
      klDiv (Measure.map (fun z ↦ (opt z.1, obs z)) rho)
        (q.prod (Measure.map obs rho)) ≠ ∞ := by
    have hoptz : Measurable (fun z : X × Fin k ↦ opt z.1) := hopt.comp measurable_fst
    have hswapFinite := InformationTheory.finite_range_mutualInformation_ne_top rho
      obs (fun z : X × Fin k ↦ opt z.1) hobs hoptz
    have hoptMarg : Measure.map (fun z : X × Fin k ↦ opt z.1) rho = q := by
      calc
        Measure.map (fun z : X × Fin k ↦ opt z.1) rho =
            Measure.map opt (Measure.map Prod.fst rho) := by
          rw [Measure.map_map hopt measurable_fst]
          rfl
        _ = Measure.map opt R := by rw [show Measure.map Prod.fst rho = R by simp [rho]]
        _ = q := rfl
    rw [hoptMarg] at hswapFinite
    have hsjoint : Measure.map Prod.swap
        (Measure.map (fun z ↦ (opt z.1, obs z)) rho) =
        Measure.map (fun z ↦ (obs z, opt z.1)) rho := by
      rw [Measure.map_map measurable_swap (hoptz.prodMk hobs)]
      rfl
    have hsref : Measure.map Prod.swap (q.prod (Measure.map obs rho)) =
        (Measure.map obs rho).prod q := Measure.prod_swap
    have hmap := InformationTheory.klDiv_map_measurableEmbedding
      (MeasurableEquiv.prodComm.measurableEmbedding :
        MeasurableEmbedding
          (Prod.swap : (Fin k × (Fin k × Set.Icc (0 : ℝ) 1)) →
            ((Fin k × Set.Icc (0 : ℝ) 1) × Fin k)))
      (Measure.map (fun z ↦ (opt z.1, obs z)) rho)
      (q.prod (Measure.map obs rho))
    change klDiv (Measure.map Prod.swap
        (Measure.map (fun z ↦ (opt z.1, obs z)) rho))
        (Measure.map Prod.swap (q.prod (Measure.map obs rho))) =
      klDiv (Measure.map (fun z ↦ (opt z.1, obs z)) rho)
        (q.prod (Measure.map obs rho)) at hmap
    rw [hsjoint, hsref] at hmap
    rw [← hmap]
    exact hswapFinite
  have hdoubleExpanded :
      klDiv (Measure.map (fun z ↦ (opt z.1, obs z)) rho)
          (q.prod (Measure.map obs rho)) =
        ∑ a, (∑ b, klDiv (Praw a b) (M b) * q {b}) * q {a} := by
    rw [hdoubleEq, MeasureTheory.lintegral_fintype]
    apply Finset.sum_congr rfl
    intro a ha
    rw [MeasureTheory.lintegral_fintype]
  have hdiagRaw :
      (∑ a, q {a} ^ 2 * klDiv (Praw a a) (M a)) ≤
        klDiv (Measure.map (fun z ↦ (opt z.1, obs z)) rho)
          (q.prod (Measure.map obs rho)) := by
    rw [hdoubleExpanded]
    apply Finset.sum_le_sum
    intro a ha
    calc
      q {a} ^ 2 * klDiv (Praw a a) (M a) =
          (klDiv (Praw a a) (M a) * q {a}) * q {a} := by ring
      _ ≤ (∑ b, klDiv (Praw a b) (M b) * q {b}) * q {a} := by
        gcongr
        exact Finset.single_le_sum
          (fun b hb ↦ show (0 : ℝ≥0∞) ≤ klDiv (Praw a b) (M b) * q {b} from bot_le)
          (Finset.mem_univ a)
  have hPfinite : ∀ a, klDiv (P a) (M a) ≠ ∞ := by
    intro a
    by_cases ha : q {a} = 0
    · dsimp [P]
      rw [if_pos ha, klDiv_self]
      exact ENNReal.zero_ne_top
    · have hone : q {a} ^ 2 * klDiv (Praw a a) (M a) ≤
          ∑ b, q {b} ^ 2 * klDiv (Praw b b) (M b) := by
        exact Finset.single_le_sum
          (fun b hb ↦ show (0 : ℝ≥0∞) ≤ q {b} ^ 2 * klDiv (Praw b b) (M b) from bot_le)
          (Finset.mem_univ a)
      have hterm : q {a} ^ 2 * klDiv (Praw a a) (M a) ≠ ∞ :=
        ne_top_of_le_ne_top hinfoFinite (hone.trans hdiagRaw)
      have hqa2 : q {a} ^ 2 ≠ 0 := pow_ne_zero 2 ha
      have hraw : klDiv (Praw a a) (M a) ≠ ∞ := by
        intro htop
        apply hterm
        rw [htop, ENNReal.mul_top hqa2]
      dsimp [P]
      rw [if_neg ha]
      exact hraw
  refine ⟨p, P, M, hPprob, hMprob, ?_, ?_, ?_⟩
  · exact hPfinite
  · let rfun : X × Fin k → ℝ := fun z ↦ (reward z.2 z.1).1
    let ropt : X → ℝ := fun x ↦ (reward (opt x) x).1
    have hrfun : Measurable rfun := by
      apply measurable_from_prod_countable_left
      intro a
      exact continuous_subtype_val.measurable.comp (hreward a)
    have hropt : Measurable ropt := by
      exact hrfun.comp (measurable_id.prodMk hopt)
    have hrfunInt : Integrable rfun rho := by
      apply Integrable.of_bound hrfun.aestronglyMeasurable 1
      exact Filter.Eventually.of_forall fun z ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (reward z.2 z.1).2.1]
        exact (reward z.2 z.1).2.2
    have hroptR : Integrable ropt R := by
      apply Integrable.of_bound hropt.aestronglyMeasurable 1
      exact Filter.Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (reward (opt x) x).2.1]
        exact (reward (opt x) x).2.2
    have hroptProd : Integrable (fun z : X × Fin k ↦ ropt z.1) rho := by
      apply Integrable.of_bound (hropt.comp measurable_fst).aestronglyMeasurable 1
      exact Filter.Eventually.of_forall fun z ↦ by
        change |(reward (opt z.1) z.1).1| ≤ 1
        rw [abs_of_nonneg (reward (opt z.1) z.1).2.1]
        exact (reward (opt z.1) z.1).2.2
    have hoptProdEq : (∫ z : X × Fin k, ropt z.1 ∂rho) = ∫ x, ropt x ∂R := by
      dsimp [rho]
      rw [MeasureTheory.integral_prod _ hroptProd]
      simp
    have hplayedEq : (∫ z, rfun z ∂rho) =
        ∑ a, p a * ∫ x, (reward a x).1 ∂R := by
      dsimp [rho] at hrfunInt ⊢
      rw [MeasureTheory.integral_prod_symm _ hrfunInt,
        MeasureTheory.integral_fintype (MeasureTheory.Integrable.of_finite)]
      apply Finset.sum_congr rfl
      intro a ha
      rfl
    let gropt : Fin k × X → ℝ := fun z ↦ (reward z.1 z.2).1
    have hgropt : Measurable gropt := by
      apply measurable_from_prod_countable_right
      intro a
      exact continuous_subtype_val.measurable.comp (hreward a)
    have hgroptInt : Integrable gropt (q ⊗ₘ K) := by
      apply Integrable.of_bound hgropt.aestronglyMeasurable 1
      exact Filter.Eventually.of_forall fun z ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (reward z.1 z.2).2.1]
        exact (reward z.1 z.2).2.2
    have hoptimalEq : (∫ x, ropt x ∂R) =
        ∑ a, p a * ∫ x, (reward a x).1 ∂K a := by
      have hpair : Measurable (fun x ↦ (opt x, x)) := hopt.prodMk measurable_id
      calc
        (∫ x, ropt x ∂R) =
            ∫ z, gropt z ∂Measure.map (fun x ↦ (opt x, x)) R := by
          rw [MeasureTheory.integral_map hpair.aemeasurable hgropt.aestronglyMeasurable]
        _ = ∫ z, gropt z ∂q ⊗ₘ K := by rw [hdis]
        _ = ∫ a, (∫ x, gropt (a, x) ∂K a) ∂q := by
          exact Measure.integral_compProd hgroptInt
        _ = ∑ a, p a * ∫ x, (reward a x).1 ∂K a := by
          rw [MeasureTheory.integral_fintype (MeasureTheory.Integrable.of_finite)]
          apply Finset.sum_congr rfl
          intro a ha
          rfl
    rw [show (∫ z, ((reward (opt z.1) z.1).1 - (reward z.2 z.1).1) ∂rho) =
        (∫ z, ropt z.1 ∂rho) - ∫ z, rfun z ∂rho by
      exact MeasureTheory.integral_sub hroptProd hrfunInt]
    rw [hoptProdEq, hoptimalEq, hplayedEq]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    have hMint : (∫ z, z.1 ∂M a) = ∫ x, (reward a x).1 ∂R := by
      change (∫ z, z.1 ∂Measure.map (reward a) R) = _
      rw [MeasureTheory.integral_map (hreward a).aemeasurable
        continuous_subtype_val.measurable.aestronglyMeasurable]
    by_cases hqa : q {a} = 0
    · have hpzero : p a = 0 := by simp [p, measureReal_def, hqa]
      rw [hpzero]
      simp
    · have hPint : (∫ z, z.1 ∂P a) = ∫ x, (reward a x).1 ∂K a := by
        dsimp [P]
        rw [if_neg hqa]
        dsimp [Praw]
        rw [MeasureTheory.integral_map (hreward a).aemeasurable
          continuous_subtype_val.measurable.aestronglyMeasurable]
      rw [hPint, hMint]
      ring
  · have hdiagPEq :
        (∑ a, ENNReal.ofReal (p a ^ 2) * klDiv (P a) (M a)) =
          ∑ a, q {a} ^ 2 * klDiv (Praw a a) (M a) := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hqa : q {a} = 0
      · simp [p, P, hqa, measureReal_def]
      · have hqtop : q {a} ≠ ∞ := measure_ne_top q {a}
        simp [p, P, hqa, measureReal_def, ENNReal.ofReal_pow,
          ENNReal.ofReal_toReal hqtop]
    have hdiagP :
        (∑ a, ENNReal.ofReal (p a ^ 2) * klDiv (P a) (M a)) ≤
          klDiv (Measure.map (fun z ↦ (opt z.1, obs z)) rho)
            (q.prod (Measure.map obs rho)) := by
      rw [hdiagPEq]
      exact hdiagRaw
    have hreal := ENNReal.toReal_mono hinfoFinite hdiagP
    rw [ENNReal.toReal_sum] at hreal
    · simpa [ENNReal.toReal_mul, sq_nonneg] using hreal
    · intro a ha
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hPfinite a)

end BanditAlgorithm

