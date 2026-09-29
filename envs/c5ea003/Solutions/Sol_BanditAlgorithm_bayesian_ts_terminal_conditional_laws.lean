-- Prove2me | solution 1 for BanditAlgorithm.bayesian_ts_terminal_conditional_laws
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T04:31:16.560554+00:00
-- url     : https://prove2.me/submissions/32877da3-c34d-4d22-803e-bdf4123a4a60

import Definitions.Def_BayesianTSRoundConditionalGains
import Theorems.Thm_BanditAlgorithm_bayesianAdversarialMeasure_prefix_marginal
import Mathlib.Probability.Kernel.CompProdEqIff

open MeasureTheory ProbabilityTheory InformationTheory

namespace BanditAlgorithm

private theorem terminal_history_action_joint_eq_step
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (pi : BanditPolicy k) (t : Fin n) :
    let terminal := bayesianAdversarialMeasure Q pi n le_rfl
    let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
    let base := bayesianAdversarialMeasure Q pi t.1 (Nat.le_of_lt t.2)
    Measure.map (fun p ↦ (history p, (p.1, (p.2 t).1))) terminal =
      Measure.map (fun z ↦ (z.1.2, (z.1.1, z.2.1)))
        (base ⊗ₘ bayesianAdversarialStepKernel pi t.1 t) := by
  dsimp only
  let terminal := bayesianAdversarialMeasure Q pi n le_rfl
  let prefixNext := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    (p.1, fun s : Fin (t.1 + 1) ↦
      p.2 (Fin.castLE (Nat.succ_le_iff.mpr t.2) s))
  let extract := fun p : (Fin n → Fin k → ℝ) × BanditHistory k (t.1 + 1) ↦
    ((fun s : Fin t.1 ↦ p.2 s.castSucc), (p.1, (p.2 (Fin.last t.1)).1))
  have hprefix := bayesianAdversarialMeasure_prefix_marginal Q pi n le_rfl
    (t.1 + 1) (Nat.succ_le_iff.mpr t.2)
  have hprefixMeas : Measurable prefixNext := by
    apply measurable_fst.prodMk
    apply measurable_pi_lambda
    intro s
    exact (measurable_pi_apply (Fin.castLE (Nat.succ_le_iff.mpr t.2) s)).comp measurable_snd
  have hextract : Measurable extract := by
    have hh : Measurable (fun p : (Fin n → Fin k → ℝ) ×
        BanditHistory k (t.1 + 1) ↦ fun s : Fin t.1 ↦ p.2 s.castSucc) := by
      apply measurable_pi_lambda
      intro s
      exact (measurable_pi_apply s.castSucc).comp measurable_snd
    apply hh.prodMk
    exact measurable_fst.prodMk
      (measurable_fst.comp ((measurable_pi_apply (Fin.last t.1)).comp measurable_snd))
  calc
    Measure.map
        (fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
          ((fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)),
            (p.1, (p.2 t).1))) terminal =
        Measure.map extract (Measure.map prefixNext terminal) := by
      rw [Measure.map_map hextract hprefixMeas]
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun p ↦ by
        congr
    _ = Measure.map extract
        (bayesianAdversarialMeasure Q pi (t.1 + 1)
          (Nat.succ_le_iff.mpr t.2)) := by rw [hprefix]
    _ = Measure.map (fun z ↦ (z.1.2, (z.1.1, z.2.1)))
        ((bayesianAdversarialMeasure Q pi t.1 (Nat.le_of_lt t.2)) ⊗ₘ
          bayesianAdversarialStepKernel pi t.1 t) := by
      rw [bayesianAdversarialMeasure, Measure.map_map]
      · apply Measure.map_congr
        exact Filter.Eventually.of_forall fun z ↦ by
          simp [extract]
      · exact hextract
      · exact (measurable_fst.comp measurable_fst).prodMk
          (measurable_banditHistorySnoc.comp
            ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

private theorem step_action_marginal
    {k n : ℕ} (pi : BanditPolicy k) (u : ℕ) (t : Fin n) :
    (bayesianAdversarialStepKernel pi u t).map Prod.fst =
      (pi.select u).comap Prod.snd measurable_snd := by
  rw [bayesianAdversarialStepKernel]
  let κ : Kernel ((Fin n → Fin k → ℝ) × BanditHistory k u) (Fin k) :=
    (pi.select u).comap Prod.snd measurable_snd
  let η : Kernel (((Fin n → Fin k → ℝ) × BanditHistory k u) × Fin k) ℝ :=
    Kernel.deterministic (fun p ↦ p.1.1 t p.2)
      (measurable_from_prod_countable_left fun a ↦
        (measurable_pi_apply a).comp ((measurable_pi_apply t).comp measurable_fst))
  change (κ ⊗ₖ η).map Prod.fst = κ
  rw [← Kernel.fst_eq]
  exact Kernel.fst_compProd κ η

private theorem terminal_history_action_joint_eq_base_action
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (pi : BanditPolicy k) (t : Fin n) :
    let terminal := bayesianAdversarialMeasure Q pi n le_rfl
    let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
    let base := bayesianAdversarialMeasure Q pi t.1 (Nat.le_of_lt t.2)
    Measure.map (fun p ↦ (history p, (p.1, (p.2 t).1))) terminal =
      Measure.map (fun z ↦ (z.1.2, (z.1.1, z.2)))
        (base ⊗ₘ (pi.select t.1).comap Prod.snd measurable_snd) := by
  dsimp only
  rw [terminal_history_action_joint_eq_step Q pi t]
  let step := bayesianAdversarialStepKernel pi t.1 t
  let base := bayesianAdversarialMeasure Q pi t.1 (Nat.le_of_lt t.2)
  let psi := fun z : ((Fin n → Fin k → ℝ) × BanditHistory k t.1) × Fin k ↦
    (z.1.2, (z.1.1, z.2))
  have hpsi : Measurable psi := by
    exact (measurable_snd.comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hmap : base ⊗ₘ (step.map Prod.fst) =
      (base ⊗ₘ step).map (Prod.map id Prod.fst) :=
    Measure.compProd_map measurable_fst
  rw [step_action_marginal pi t.1 t] at hmap
  rw [hmap, Measure.map_map hpsi]
  · rfl
  · exact measurable_id.prodMap measurable_fst

private theorem base_action_eq_history_posterior_prod
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (pi : BanditPolicy k) (t : Fin n) :
    let base := bayesianAdversarialMeasure Q pi t.1 (Nat.le_of_lt t.2)
    let nu := Measure.map Prod.snd base
    let post := condDistrib Prod.fst Prod.snd base
    let act := pi.select t.1
    Measure.map (fun z ↦ (z.1.2, (z.1.1, z.2)))
        (base ⊗ₘ act.comap Prod.snd measurable_snd) =
      nu ⊗ₘ (post.prod act) := by
  dsimp only
  let base := bayesianAdversarialMeasure Q pi t.1 (Nat.le_of_lt t.2)
  let nu := Measure.map Prod.snd base
  let post := condDistrib Prod.fst Prod.snd base
  let act := pi.select t.1
  have hdis : nu ⊗ₘ post = Measure.map Prod.swap base := by
    dsimp [nu, post]
    exact compProd_map_condDistrib measurable_fst.aemeasurable
  apply Measure.ext_prod₃
  intro s u v hs hu hv
  have hpsi : Measurable
      (fun z : ((Fin n → Fin k → ℝ) × BanditHistory k t.1) × Fin k ↦
        (z.1.2, (z.1.1, z.2))) :=
    (measurable_snd.comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  rw [Measure.map_apply hpsi (hs.prod (hu.prod hv))]
  have hpre :
      (fun z : ((Fin n → Fin k → ℝ) × BanditHistory k t.1) × Fin k ↦
        (z.1.2, (z.1.1, z.2))) ⁻¹' (s ×ˢ (u ×ˢ v)) = (u ×ˢ s) ×ˢ v := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod]
    aesop
  rw [hpre, Measure.compProd_apply_prod (hu.prod hs) hv]
  change (∫⁻ z in u ×ˢ s, act z.2 v ∂base) =
    (nu ⊗ₘ (post.prod act)) (s ×ˢ (u ×ˢ v))
  rw [Measure.compProd_apply_prod hs (hu.prod hv)]
  simp_rw [Kernel.prod_apply]
  simp_rw [Measure.prod_prod]
  change (∫⁻ z in u ×ˢ s, act z.2 v ∂base) =
    ∫⁻ h in s, post h u * act h v ∂nu
  have hleft : (∫⁻ z in u ×ˢ s, act z.2 v ∂base) =
      ∫⁻ z in s ×ˢ u, act z.1 v ∂Measure.map Prod.swap base := by
    symm
    change (∫⁻ z in s ×ˢ u, ((fun h ↦ act h v) ∘ Prod.fst) z
        ∂Measure.map Prod.swap base) = _
    rw [MeasureTheory.setLIntegral_map (hs.prod hu)
      ((Kernel.measurable_coe act hv).comp measurable_fst) measurable_swap,
      Set.preimage_swap_prod]
    rfl
  rw [hleft, ← hdis]
  change (∫⁻ z in s ×ˢ u, ((fun h ↦ act h v) ∘ Prod.fst) z
      ∂nu ⊗ₘ post) = _
  rw [Measure.setLIntegral_compProd
    ((Kernel.measurable_coe act hv).comp measurable_fst) hs hu]
  apply MeasureTheory.setLIntegral_congr_fun hs
  intro h hh
  change (∫⁻ _ in u, act h v ∂post h) = post h u * act h v
  rw [MeasureTheory.setLIntegral_const]
  exact mul_comm _ _

private theorem terminal_conditional_matrix_action_eq_prod
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (pi : BanditPolicy k) (t : Fin n) :
    let terminal := bayesianAdversarialMeasure Q pi n le_rfl
    let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
    let base := bayesianAdversarialMeasure Q pi t.1 (Nat.le_of_lt t.2)
    let nu := Measure.map history terminal
    let post := condDistrib Prod.fst Prod.snd base
    condDistrib (fun p ↦ (p.1, (p.2 t).1)) history terminal =ᵐ[nu]
      post.prod (pi.select t.1) := by
  dsimp only
  let terminal := bayesianAdversarialMeasure Q pi n le_rfl
  let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
  let base := bayesianAdversarialMeasure Q pi t.1 (Nat.le_of_lt t.2)
  let nu := Measure.map history terminal
  let post := condDistrib Prod.fst Prod.snd base
  have hhistory : Measurable history := by
    apply measurable_pi_lambda
    intro s
    exact (measurable_pi_apply (Fin.castLE (Nat.le_of_lt t.2) s)).comp measurable_snd
  have hjoint : Measurable
      (fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
        (p.1, (p.2 t).1)) :=
    measurable_fst.prodMk
      (measurable_fst.comp ((measurable_pi_apply t).comp measurable_snd))
  have hnu : nu = Measure.map Prod.snd base := by
    have hp := bayesianAdversarialMeasure_prefix_marginal Q pi n le_rfl
      t.1 (Nat.le_of_lt t.2)
    have hprefix : Measurable
        (fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
          (p.1, history p)) := measurable_fst.prodMk hhistory
    have hm := congrArg (Measure.map (@Prod.snd
      (Fin n → Fin k → ℝ) (BanditHistory k t.1))) hp
    rw [Measure.map_map measurable_snd hprefix] at hm
    simpa [nu, Function.comp_def] using hm
  apply condDistrib_ae_eq_of_measure_eq_compProd history hjoint.aemeasurable
  calc
    Measure.map (fun p ↦ (history p, (p.1, (p.2 t).1))) terminal =
        Measure.map (fun z ↦ (z.1.2, (z.1.1, z.2)))
          (base ⊗ₘ (pi.select t.1).comap Prod.snd measurable_snd) := by
      exact terminal_history_action_joint_eq_base_action Q pi t
    _ = Measure.map Prod.snd base ⊗ₘ (post.prod (pi.select t.1)) := by
      exact base_action_eq_history_posterior_prod Q pi t
    _ = nu ⊗ₘ (post.prod (pi.select t.1)) := by rw [hnu]

private theorem terminal_conditional_matrix_eq_base_posterior
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (pi : BanditPolicy k) (t : Fin n) :
    let terminal := bayesianAdversarialMeasure Q pi n le_rfl
    let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
    let base := bayesianAdversarialMeasure Q pi t.1 (Nat.le_of_lt t.2)
    let nu := Measure.map history terminal
    condDistrib Prod.fst history terminal =ᵐ[nu]
      condDistrib Prod.fst Prod.snd base := by
  dsimp only
  let terminal := bayesianAdversarialMeasure Q pi n le_rfl
  let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
  let base := bayesianAdversarialMeasure Q pi t.1 (Nat.le_of_lt t.2)
  let nu := Measure.map history terminal
  let post := condDistrib Prod.fst Prod.snd base
  have hhistory : Measurable history := by
    apply measurable_pi_lambda
    intro s
    exact (measurable_pi_apply (Fin.castLE (Nat.le_of_lt t.2) s)).comp measurable_snd
  have hp := bayesianAdversarialMeasure_prefix_marginal Q pi n le_rfl
    t.1 (Nat.le_of_lt t.2)
  have hprefix : Measurable
      (fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
        (p.1, history p)) := measurable_fst.prodMk hhistory
  have hnu : nu = Measure.map Prod.snd base := by
    have hm := congrArg (Measure.map (@Prod.snd
      (Fin n → Fin k → ℝ) (BanditHistory k t.1))) hp
    rw [Measure.map_map measurable_snd hprefix] at hm
    simpa [nu, Function.comp_def] using hm
  apply condDistrib_ae_eq_of_measure_eq_compProd history measurable_fst.aemeasurable
  calc
    Measure.map (fun p ↦ (history p, p.1)) terminal =
        Measure.map Prod.swap (Measure.map (fun p ↦ (p.1, history p)) terminal) := by
      rw [Measure.map_map measurable_swap hprefix]
      rfl
    _ = Measure.map Prod.swap base := by rw [hp]
    _ = Measure.map Prod.snd base ⊗ₘ post := by
      exact (compProd_map_condDistrib measurable_fst.aemeasurable).symm
    _ = nu ⊗ₘ post := by rw [hnu]



set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory

private theorem terminal_observed_reward_eq_matrix_reward
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (pi : BanditPolicy k) (t : Fin n) :
    let terminal := bayesianAdversarialMeasure Q pi n le_rfl
    ∀ᵐ z ∂terminal, z.2 t = ((z.2 t).1, z.1 t (z.2 t).1) := by
  dsimp only
  let terminal := bayesianAdversarialMeasure Q pi n le_rfl
  let prefixNext := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    (p.1, fun s : Fin (t.1 + 1) ↦
      p.2 (Fin.castLE (Nat.succ_le_iff.mpr t.2) s))
  have hprefix := bayesianAdversarialMeasure_prefix_marginal Q pi n le_rfl
    (t.1 + 1) (Nat.succ_le_iff.mpr t.2)
  have hprefixMeas : Measurable prefixNext := by
    apply measurable_fst.prodMk
    apply measurable_pi_lambda
    intro s
    exact (measurable_pi_apply (Fin.castLE (Nat.succ_le_iff.mpr t.2) s)).comp measurable_snd
  have hgood : ∀ᵐ z ∂bayesianAdversarialMeasure Q pi (t.1 + 1)
      (Nat.succ_le_iff.mpr t.2),
      z.2 (Fin.last t.1) =
        ((z.2 (Fin.last t.1)).1, z.1 t (z.2 (Fin.last t.1)).1) := by
    rw [bayesianAdversarialMeasure]
    let assemble := fun p :
        ((Fin n → Fin k → ℝ) × BanditHistory k t.1) × (Fin k × ℝ) ↦
      (p.1.1, Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1.2 p.2)
    have hassemble : Measurable assemble :=
      (measurable_fst.comp measurable_fst).prodMk
        (measurable_banditHistorySnoc.comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    let lastObs := fun z : (Fin n → Fin k → ℝ) × BanditHistory k (t.1 + 1) ↦
      z.2 (Fin.last t.1)
    let matrixObs := fun z : (Fin n → Fin k → ℝ) × BanditHistory k (t.1 + 1) ↦
      ((z.2 (Fin.last t.1)).1, z.1 t (z.2 (Fin.last t.1)).1)
    have hlastObs : Measurable lastObs :=
      (measurable_pi_apply (Fin.last t.1)).comp measurable_snd
    have heval : Measurable
        (fun z : (Fin n → Fin k → ℝ) × Fin k ↦ z.1 t z.2) :=
      measurable_from_prod_countable_left fun a ↦
        (measurable_pi_apply a).comp (measurable_pi_apply t)
    have hmatrixObs : Measurable matrixObs := by
      exact (measurable_fst.comp hlastObs).prodMk
        (heval.comp (measurable_fst.prodMk (measurable_fst.comp hlastObs)))
    change ∀ᵐ z ∂Measure.map assemble
        (bayesianAdversarialMeasure Q pi t.1 (Nat.le_of_lt t.2) ⊗ₘ
          bayesianAdversarialStepKernel pi t.1 t),
      z.2 (Fin.last t.1) =
        ((z.2 (Fin.last t.1)).1, z.1 t (z.2 (Fin.last t.1)).1)
    change ∀ᵐ z ∂Measure.map assemble
        (bayesianAdversarialMeasure Q pi t.1 (Nat.le_of_lt t.2) ⊗ₘ
          bayesianAdversarialStepKernel pi t.1 t), lastObs z = matrixObs z
    refine (ae_map_iff hassemble.aemeasurable
      (measurableSet_eq_fun hlastObs hmatrixObs)).2 ?_
    apply Measure.ae_compProd_of_ae_ae
    · exact measurableSet_eq_fun (hlastObs.comp hassemble) (hmatrixObs.comp hassemble)
    · filter_upwards with x
      simp only [lastObs, matrixObs, assemble, Fin.snoc_last]
      change ∀ᵐ b ∂bayesianAdversarialStepKernel pi t.1 t x,
        b = (b.1, x.1 t b.1)
      rw [bayesianAdversarialStepKernel]
      let act : Kernel ((Fin n → Fin k → ℝ) × BanditHistory k t.1) (Fin k) :=
        (pi.select t.1).comap Prod.snd measurable_snd
      let readReward := fun p :
          ((Fin n → Fin k → ℝ) × BanditHistory k t.1) × Fin k ↦ p.1.1 t p.2
      have hreadReward : Measurable readReward :=
        measurable_from_prod_countable_left fun a ↦
          (measurable_pi_apply a).comp
            ((measurable_pi_apply t).comp measurable_fst)
      change ∀ᵐ ar ∂(act ⊗ₖ Kernel.deterministic readReward hreadReward) x,
        ar = (ar.1, x.1 t ar.1)
      apply Kernel.ae_compProd_of_ae_ae
      · exact measurableSet_eq_fun measurable_id
          (measurable_fst.prodMk
            ((measurable_of_finite (fun a : Fin k ↦ x.1 t a)).comp measurable_fst))
      · filter_upwards with a
        rw [Kernel.deterministic_apply]
        simp [readReward]
  have hgood' : ∀ᵐ z ∂Measure.map prefixNext terminal,
      z.2 (Fin.last t.1) =
        ((z.2 (Fin.last t.1)).1, z.1 t (z.2 (Fin.last t.1)).1) := by
    rw [hprefix]
    exact hgood
  have hpull := ae_of_ae_map hprefixMeas.aemeasurable hgood'
  filter_upwards [hpull] with z hz
  simpa [prefixNext] using hz


theorem _root_.solution
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (pi : BanditPolicy k) (t : Fin n) :
    let terminal := bayesianAdversarialMeasure Q pi n le_rfl
    let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
    let base := bayesianAdversarialMeasure Q pi t.1 (Nat.le_of_lt t.2)
    let nu := Measure.map history terminal
    let post := condDistrib Prod.fst Prod.snd base
    (condDistrib Prod.fst history terminal =ᵐ[nu] post) ∧
    (condDistrib (fun p ↦ (p.1, (p.2 t).1)) history terminal =ᵐ[nu]
      post.prod (pi.select t.1)) ∧
    (∀ᵐ z ∂terminal, z.2 t = ((z.2 t).1, z.1 t (z.2 t).1)) := by
  dsimp only
  exact ⟨terminal_conditional_matrix_eq_base_posterior Q pi t,
    terminal_conditional_matrix_action_eq_prod Q pi t,
    terminal_observed_reward_eq_matrix_reward Q pi t⟩

end BanditAlgorithm

