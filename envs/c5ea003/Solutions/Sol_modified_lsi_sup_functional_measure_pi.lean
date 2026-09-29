-- Prove2me | solution 1 for modified_lsi_sup_functional_measure_pi
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-24T18:23:32.115903+00:00
-- url     : https://prove2.me/submissions/d440d1c5-f594-4029-94b4-dd974a8b30bc

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_bousquet_massart_modified_lsi_summand_psi
import Theorems.Thm_entropy_n_coordinate_han_subadditivity_measure_pi_pos
open Real MeasureTheory

/-! ## Reusable helpers -/

/-- Bounded measurable function on a probability measure is integrable. -/
private theorem bdd_int {β : Type*} [MeasurableSpace β] (κ : Measure β) [IsProbabilityMeasure κ]
    (F : β → ℝ) (M : ℝ) (hF : Measurable F) (hb : ∀ x, ‖F x‖ ≤ M) : Integrable F κ :=
  Integrable.of_bound hF.aestronglyMeasurable M (ae_of_all _ hb)

/-- `Real.log` is bounded on `[cc, CC]` (cc > 0). -/
private theorem log_bd {cc CC v : ℝ} (hcpos : 0 < cc) (hlo : cc ≤ v) (hhi : v ≤ CC) :
    |Real.log v| ≤ |Real.log cc| + |Real.log CC| := by
  have h1 : Real.log cc ≤ Real.log v := Real.log_le_log hcpos hlo
  have h2 : Real.log v ≤ Real.log CC := Real.log_le_log (lt_of_lt_of_le hcpos hlo) hhi
  rw [abs_le]
  exact ⟨by linarith [neg_abs_le (Real.log cc), abs_nonneg (Real.log CC)],
    by linarith [le_abs_self (Real.log CC), abs_nonneg (Real.log cc)]⟩

theorem upd_insertNth {m : ℕ} {α : Fin (m+1) → Type}
    (k : Fin (m+1)) (x0 t : α k) (rest : ∀ j, α (k.succAbove j)) :
    Function.update (Fin.insertNth k x0 rest) k t = Fin.insertNth k t rest := by
  ext i
  rcases eq_or_ne i k with h | h
  · subst h; simp
  · rw [Function.update_of_ne h]
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq h
    simp [Fin.insertNth_apply_succAbove]

-- Single integral transport at coordinate k.
theorem transport_at_k {m : ℕ} {α : Fin (m+1) → Type} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (k : Fin (m+1)) (F : (∀ i, α i) → ℝ) :
    ∫ x, F x ∂(Measure.pi μ)
      = ∫ p : α k × (∀ j, α (k.succAbove j)),
          F (Fin.insertNth k p.1 p.2)
          ∂((μ k).prod (Measure.pi (fun j => μ (k.succAbove j)))) := by
  have hmp := measurePreserving_piFinSuccAbove μ k
  rw [← hmp.integral_comp (MeasurableEquiv.piFinSuccAbove α k).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with x
  have : Fin.insertNth k ((MeasurableEquiv.piFinSuccAbove α k) x).1
      ((MeasurableEquiv.piFinSuccAbove α k) x).2
      = (MeasurableEquiv.piFinSuccAbove α k).symm ((MeasurableEquiv.piFinSuccAbove α k) x) := rfl
  rw [this, MeasurableEquiv.symm_apply_apply]

set_option maxHeartbeats 1600000 in
theorem per_coord_bound {m : ℕ} {α : Fin (m+1) → Type} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : (∀ i, α i) → ℝ) (Zk : (∀ i, α i) → ℝ) (lam : ℝ) (k : Fin (m+1))
    (hZmeas : Measurable Z) (hZkmeas : Measurable Zk)
    (hZk_indep : ∀ x t, Zk (Function.update x k t) = Zk x)
    (cc CC Dzk : ℝ) (hcpos : 0 < cc)
    (hglb : ∀ x, cc ≤ Real.exp (lam * Z x))
    (hgub : ∀ x, Real.exp (lam * Z x) ≤ CC)
    (hZkbd : ∀ x, |Zk x| ≤ Dzk) :
    (∫ x, Real.exp (lam * Z x) * Real.log (Real.exp (lam * Z x)) ∂(Measure.pi μ))
      - ∫ x, (∫ t, Real.exp (lam * Z (Function.update x k t)) ∂(μ k))
          * Real.log (∫ t, Real.exp (lam * Z (Function.update x k t)) ∂(μ k)) ∂(Measure.pi μ)
    ≤ ∫ x, Real.exp (lam * Z x)
        * (Real.exp (-(lam * (Z x - Zk x))) - 1 + lam * (Z x - Zk x)) ∂(Measure.pi μ) := by
  classical
  -- The fiber function: gf rest s = exp(λ Z(insertNth k s rest))
  set g : (∀ i, α i) → ℝ := fun x => Real.exp (lam * Z x) with hg
  set ν : Measure (∀ j, α (k.succAbove j)) := Measure.pi (fun j => μ (k.succAbove j)) with hν
  have hνprob : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  -- measurability of g
  have hgmeas : Measurable g := (hZmeas.const_mul lam).exp
  -- g bounded
  have hglb' : ∀ x, cc ≤ g x := hglb
  have hgub' : ∀ x, g x ≤ CC := hgub
  have hgnn : ∀ x, 0 ≤ g x := fun x => le_of_lt (lt_of_lt_of_le hcpos (hglb x))
  -- each α i nonempty (from probability measure), hence the full pi type
  have hαne : ∀ i, Nonempty (α i) := by
    intro i
    by_contra h
    rw [not_nonempty_iff] at h
    have h0 : (μ i) Set.univ = 0 := by rw [Set.univ_eq_empty_iff.2 h]; simp
    have := (measure_univ (μ := μ i)); rw [h0] at this; exact one_ne_zero this.symm
  have hpine : Nonempty (∀ i, α i) := ⟨fun i => (hαne i).some⟩
  -- bound on lam * Z x : log cc ≤ lam Z x ≤ log CC
  have hcCpos : 0 < CC := lt_of_lt_of_le hcpos (le_trans (hglb hpine.some) (hgub hpine.some))
  have hlamZ_lb : ∀ x, Real.log cc ≤ lam * Z x := by
    intro x
    have := hglb x
    calc Real.log cc ≤ Real.log (Real.exp (lam * Z x)) := Real.log_le_log hcpos this
      _ = lam * Z x := Real.log_exp _
  have hlamZ_ub : ∀ x, lam * Z x ≤ Real.log CC := by
    intro x
    have := hgub x
    calc lam * Z x = Real.log (Real.exp (lam * Z x)) := (Real.log_exp _).symm
      _ ≤ Real.log CC := Real.log_le_log (Real.exp_pos _) this
  have hlamZ_bd : ∀ x, |lam * Z x| ≤ |Real.log cc| + |Real.log CC| := by
    intro x
    rw [abs_le]
    constructor
    · calc -(|Real.log cc| + |Real.log CC|) ≤ Real.log cc := by
            have := abs_nonneg (Real.log CC); have := neg_abs_le (Real.log cc); linarith [neg_abs_le (Real.log cc), abs_nonneg (Real.log CC)]
          _ ≤ lam * Z x := hlamZ_lb x
    · calc lam * Z x ≤ Real.log CC := hlamZ_ub x
          _ ≤ |Real.log cc| + |Real.log CC| := by linarith [le_abs_self (Real.log CC), abs_nonneg (Real.log cc)]
  -- generic bounded-integrable helper on a probability measure
  have hint : ∀ {β : Type} [MeasurableSpace β] (κ : Measure β) [IsProbabilityMeasure κ]
      (F : β → ℝ) (M : ℝ), Measurable F → (∀ x, ‖F x‖ ≤ M) → Integrable F κ := by
    intro β _ κ _ F M hF hb
    exact Integrable.of_bound hF.aestronglyMeasurable M (ae_of_all _ hb)
  -- fiber function gf rest s = g(insertNth k s rest)
  set gf : (∀ j, α (k.succAbove j)) → α k → ℝ :=
    fun rest s => g (Fin.insertNth k s rest) with hgf
  have hgf_meas : ∀ rest, Measurable (gf rest) := by
    intro rest
    refine hgmeas.comp ?_
    exact (measurable_pi_iff.2 (fun i => by
      rcases eq_or_ne i k with rfl | hik
      · simpa using measurable_id
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hik
        simpa [Fin.insertNth_apply_succAbove] using measurable_const))
  -- fiber log-rewrite: log(gf) = lam * Z(insertNth)
  have hlog_gf : ∀ rest s, Real.log (gf rest s) = lam * Z (Fin.insertNth k s rest) := by
    intro rest s; rw [hgf]; simp only [hg]; rw [Real.log_exp]
  -- gf fiber bounds + integral bounds (cc ≤ ∫ gf ≤ CC)
  have hgf_nn : ∀ rest s, 0 ≤ gf rest s := fun rest s => hgnn _
  have hgf_lb : ∀ rest s, cc ≤ gf rest s := fun rest s => hglb _
  have hgf_ub : ∀ rest s, gf rest s ≤ CC := fun rest s => hgub _
  have hgf_fib_int : ∀ rest, Integrable (gf rest) (μ k) := fun rest =>
    hint (μ k) _ CC (hgf_meas rest) (fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hgf_nn rest s)]; exact hgf_ub rest s)
  have hmlb : ∀ rest, cc ≤ ∫ s, gf rest s ∂(μ k) := by
    intro rest
    calc cc = ∫ _s, cc ∂(μ k) := by
          rw [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
      _ ≤ ∫ s, gf rest s ∂(μ k) :=
          integral_mono (integrable_const _) (hgf_fib_int rest) (fun s => hgf_lb rest s)
  have hmub : ∀ rest, ∫ s, gf rest s ∂(μ k) ≤ CC := by
    intro rest
    calc ∫ s, gf rest s ∂(μ k) ≤ ∫ _s, CC ∂(μ k) :=
          integral_mono (hgf_fib_int rest) (integrable_const _) (fun s => hgf_ub rest s)
      _ = CC := by rw [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
  -- Zk constant in coordinate k value: define cfib rest = Zk(insertNth k s rest) (any s)
  -- pick s via the fact insertNth depends on coord k only through s; but Zk indep of coord k
  -- so Zk(insertNth k s rest) is the same for all s.
  have hZk_const : ∀ rest s s', Zk (Fin.insertNth k s rest) = Zk (Fin.insertNth k s' rest) := by
    intro rest s s'
    have h1 : Function.update (Fin.insertNth k s rest) k s' = Fin.insertNth k s' rest :=
      upd_insertNth k s s' rest
    rw [← h1, hZk_indep]
  -- The fiber bound via CHILD 2, for each rest.
  have hfiber : ∀ rest : (∀ j, α (k.succAbove j)),
      (∫ s, gf rest s * Real.log (gf rest s) ∂(μ k))
        - (∫ s, gf rest s ∂(μ k)) * Real.log (∫ s, gf rest s ∂(μ k))
      ≤ ∫ s, gf rest s
          * (Real.exp (-(lam * (Z (Fin.insertNth k s rest) - Zk (Fin.insertNth k s rest))))
              - 1 + lam * (Z (Fin.insertNth k s rest) - Zk (Fin.insertNth k s rest))) ∂(μ k) := by
    intro rest
    set Zfib : α k → ℝ := fun s => Z (Fin.insertNth k s rest) with hZfib
    have hZfib_meas : Measurable Zfib := by
      refine hZmeas.comp ?_
      exact (measurable_pi_iff.2 (fun i => by
        rcases eq_or_ne i k with rfl | hik
        · simpa using measurable_id
        · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hik
          simpa [Fin.insertNth_apply_succAbove] using measurable_const))
    -- integrability of exp(lam Zfib) and lam Zfib exp(lam Zfib)
    have hexp_int : Integrable (fun s => Real.exp (lam * Zfib s)) (μ k) := by
      refine hint (μ k) _ CC ((hZfib_meas.const_mul lam).exp) (fun s => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (Real.exp_pos _))]
      exact hgub (Fin.insertNth k s rest)
    have hZexp_int : Integrable (fun s => lam * Zfib s * Real.exp (lam * Zfib s)) (μ k) := by
      refine hint (μ k) _ ((|Real.log cc| + |Real.log CC|) * CC)
        (((measurable_const.mul hZfib_meas).mul ((hZfib_meas.const_mul lam).exp))) (fun s => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_of_lt (Real.exp_pos _))]
      have h1 : |lam * Zfib s| ≤ |Real.log cc| + |Real.log CC| := hlamZ_bd (Fin.insertNth k s rest)
      have h2 : Real.exp (lam * Zfib s) ≤ CC := hgub (Fin.insertNth k s rest)
      have h3 : 0 ≤ Real.exp (lam * Zfib s) := le_of_lt (Real.exp_pos _)
      calc |lam * Zfib s| * Real.exp (lam * Zfib s)
          ≤ (|Real.log cc| + |Real.log CC|) * Real.exp (lam * Zfib s) := by
            apply mul_le_mul_of_nonneg_right h1 h3
        _ ≤ (|Real.log cc| + |Real.log CC|) * CC := by
            apply mul_le_mul_of_nonneg_left h2
            positivity
    have hC2 := bousquet_massart_modified_lsi_summand_psi (μ := μ k) (Z := Zfib) (lam := lam)
      (c := Zk (Fin.insertNth k ((hαne k).some) rest)) hexp_int hZexp_int
    -- gf rest s = exp(lam Zfib s)
    have hgf_eq : ∀ s, gf rest s = Real.exp (lam * Zfib s) := fun s => rfl
    -- LHS of hfiber = LHS of hC2
    have hLHS1 : (∫ s, gf rest s * Real.log (gf rest s) ∂(μ k))
        = lam * ∫ s, Zfib s * Real.exp (lam * Zfib s) ∂(μ k) := by
      rw [← integral_const_mul]
      apply integral_congr_ae; filter_upwards with s
      rw [hgf_eq s, Real.log_exp]; ring
    have hLHS2 : (∫ s, gf rest s ∂(μ k)) = ∫ s, Real.exp (lam * Zfib s) ∂(μ k) := by
      apply integral_congr_ae; filter_upwards with s; rw [hgf_eq s]
    -- RHS of hfiber = RHS of hC2 (Zk(ins) = c constant)
    have hRHS : (∫ s, gf rest s
          * (Real.exp (-(lam * (Z (Fin.insertNth k s rest) - Zk (Fin.insertNth k s rest))))
              - 1 + lam * (Z (Fin.insertNth k s rest) - Zk (Fin.insertNth k s rest))) ∂(μ k))
        = ∫ s, Real.exp (lam * Zfib s)
            * (Real.exp (-(lam * (Zfib s - Zk (Fin.insertNth k ((hαne k).some) rest))))
                - 1 + lam * (Zfib s - Zk (Fin.insertNth k ((hαne k).some) rest))) ∂(μ k) := by
      apply integral_congr_ae; filter_upwards with s
      rw [hgf_eq s]
      rw [hZk_const rest s ((hαne k).some)]
    rw [hLHS1, hLHS2, hRHS]
    exact hC2
  -- ===== ASSEMBLY: transport A, B, C and apply integral_mono over rest =====
  -- Aterm rest, Bterm rest, Cterm rest
  set Aterm : (∀ j, α (k.succAbove j)) → ℝ :=
    fun rest => ∫ s, gf rest s * Real.log (gf rest s) ∂(μ k) with hAterm
  set Bterm : (∀ j, α (k.succAbove j)) → ℝ :=
    fun rest => (∫ s, gf rest s ∂(μ k)) * Real.log (∫ s, gf rest s ∂(μ k)) with hBterm
  set Cterm : (∀ j, α (k.succAbove j)) → ℝ :=
    fun rest => ∫ s, gf rest s
      * (Real.exp (-(lam * (Z (Fin.insertNth k s rest) - Zk (Fin.insertNth k s rest))))
          - 1 + lam * (Z (Fin.insertNth k s rest) - Zk (Fin.insertNth k s rest))) ∂(μ k)
    with hCterm
  haveI : IsProbabilityMeasure ((μ k).prod ν) := by infer_instance
  -- log g is bounded
  have hloggbd : ∀ x, |Real.log (g x)| ≤ |Real.log cc| + |Real.log CC| := by
    intro x
    have : Real.log (g x) = lam * Z x := by simp only [hg]; rw [Real.log_exp]
    rw [this]; exact hlamZ_bd x
  -- prod-integrability helper for an integrand of (s,rest) bounded by M
  have hprodint : ∀ (F : α k × (∀ j, α (k.succAbove j)) → ℝ) (M : ℝ),
      Measurable F → (∀ p, ‖F p‖ ≤ M) → Integrable F ((μ k).prod ν) := by
    intro F M hF hb; exact hint ((μ k).prod ν) F M hF hb
  -- === A transport ===
  have hA : (∫ x, g x * Real.log (g x) ∂(Measure.pi μ)) = ∫ rest, Aterm rest ∂ν := by
    rw [transport_at_k μ k (fun x => g x * Real.log (g x))]
    have hAint : Integrable (fun p : α k × (∀ j, α (k.succAbove j)) =>
        g (Fin.insertNth k p.1 p.2) * Real.log (g (Fin.insertNth k p.1 p.2)))
        ((μ k).prod ν) := by
      refine hprodint _ (CC * (|Real.log cc| + |Real.log CC|)) ?_ (fun p => ?_)
      · exact (hgmeas.comp (MeasurableEquiv.piFinSuccAbove α k).symm.measurable).mul
          ((hgmeas.comp (MeasurableEquiv.piFinSuccAbove α k).symm.measurable).log)
      · rw [Real.norm_eq_abs, abs_mul]
        apply mul_le_mul (by rw [abs_of_nonneg (hgnn _)]; exact hgub _) (hloggbd _) (abs_nonneg _)
          (le_of_lt hcCpos)
    rw [integral_prod_symm _ hAint]
  -- the φ-argument u(x) = -(lam (Z x - Zk x)) is bounded
  let Du : ℝ := (|Real.log cc| + |Real.log CC|) + |lam| * Dzk
  have hubd : ∀ x, |(-(lam * (Z x - Zk x)))| ≤ Du := by
    intro x
    show |(-(lam * (Z x - Zk x)))| ≤ (|Real.log cc| + |Real.log CC|) + |lam| * Dzk
    have e1 : -(lam * (Z x - Zk x)) = -(lam * Z x) + lam * Zk x := by ring
    rw [e1]
    have hb1 : |(-(lam * Z x) + lam * Zk x)| ≤ |(-(lam * Z x))| + |lam * Zk x| := abs_add_le _ _
    have hbn : |(-(lam * Z x))| = |lam * Z x| := abs_neg _
    have hbm : |lam * Zk x| ≤ |lam| * Dzk := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hZkbd x) (abs_nonneg _)
    have hb5 : |lam * Z x| ≤ |Real.log cc| + |Real.log CC| := hlamZ_bd x
    rw [hbn] at hb1
    linarith [hb1, hbm, hb5]
  -- φ(u) = e^u - 1 + u bounded for |u| ≤ Du
  have hphibd : ∀ x, |(Real.exp (-(lam * (Z x - Zk x))) - 1 + lam * (Z x - Zk x))|
      ≤ Real.exp Du + 1 + Du := by
    intro x
    set u := -(lam * (Z x - Zk x)) with hu
    have hubx : |u| ≤ Du := hubd x
    have e2 : Real.exp (-(lam * (Z x - Zk x))) - 1 + lam * (Z x - Zk x)
        = Real.exp u - 1 - u := by rw [hu]; ring
    rw [e2]
    have ht1 : |Real.exp u - 1 - u| ≤ |Real.exp u - 1| + |u| := by
      have := abs_add_le (Real.exp u - 1) (-u)
      simpa [sub_eq_add_neg, abs_neg] using this
    have ht2 : |Real.exp u - 1| ≤ |Real.exp u| + |(1:ℝ)| := by
      have := abs_sub (Real.exp u) (1:ℝ)
      exact this
    have heu : |Real.exp u| ≤ Real.exp Du := by
      rw [abs_of_nonneg (le_of_lt (Real.exp_pos _))]
      exact Real.exp_le_exp.mpr (le_trans (le_abs_self u) hubx)
    have h1 : |(1:ℝ)| = 1 := abs_one
    linarith [ht1, ht2, heu, hubx, h1]
  -- measurability of Zk ∘ insertNth and Z ∘ insertNth (as functions of p)
  have hZins_meas : Measurable (fun p : α k × (∀ j, α (k.succAbove j)) =>
      Z (Fin.insertNth k p.1 p.2)) :=
    hZmeas.comp (MeasurableEquiv.piFinSuccAbove α k).symm.measurable
  have hZkins_meas : Measurable (fun p : α k × (∀ j, α (k.succAbove j)) =>
      Zk (Fin.insertNth k p.1 p.2)) :=
    hZkmeas.comp (MeasurableEquiv.piFinSuccAbove α k).symm.measurable
  -- === C transport ===
  have hC : (∫ x, g x * (Real.exp (-(lam * (Z x - Zk x))) - 1 + lam * (Z x - Zk x))
        ∂(Measure.pi μ)) = ∫ rest, Cterm rest ∂ν := by
    rw [transport_at_k μ k (fun x => g x
        * (Real.exp (-(lam * (Z x - Zk x))) - 1 + lam * (Z x - Zk x)))]
    have hCint : Integrable (fun p : α k × (∀ j, α (k.succAbove j)) =>
        g (Fin.insertNth k p.1 p.2)
          * (Real.exp (-(lam * (Z (Fin.insertNth k p.1 p.2)
                - Zk (Fin.insertNth k p.1 p.2))))
              - 1 + lam * (Z (Fin.insertNth k p.1 p.2) - Zk (Fin.insertNth k p.1 p.2))))
        ((μ k).prod ν) := by
      refine hprodint _ (CC * (Real.exp Du + 1 + Du)) ?_ (fun p => ?_)
      · exact (hgmeas.comp (MeasurableEquiv.piFinSuccAbove α k).symm.measurable).mul
          ((((hZins_meas.sub hZkins_meas).const_mul lam).neg.exp.sub measurable_const).add
            ((hZins_meas.sub hZkins_meas).const_mul lam))
      · rw [Real.norm_eq_abs, abs_mul]
        apply mul_le_mul (by rw [abs_of_nonneg (hgnn _)]; exact hgub _) (hphibd _) (abs_nonneg _)
          (le_of_lt hcCpos)
    rw [integral_prod_symm _ hCint]
  -- === B transport ===
  have hB : (∫ x, (∫ t, Real.exp (lam * Z (Function.update x k t)) ∂(μ k))
          * Real.log (∫ t, Real.exp (lam * Z (Function.update x k t)) ∂(μ k))
          ∂(Measure.pi μ)) = ∫ rest, Bterm rest ∂ν := by
    rw [transport_at_k μ k (fun x => (∫ t, Real.exp (lam * Z (Function.update x k t)) ∂(μ k))
        * Real.log (∫ t, Real.exp (lam * Z (Function.update x k t)) ∂(μ k)))]
    -- transported integrand at p equals Bterm p.2 (independent of p.1)
    have hBeq : ∀ p : α k × (∀ j, α (k.succAbove j)),
        (∫ t, Real.exp (lam * Z (Function.update (Fin.insertNth k p.1 p.2) k t)) ∂(μ k))
          * Real.log (∫ t, Real.exp (lam * Z (Function.update (Fin.insertNth k p.1 p.2) k t)) ∂(μ k))
        = Bterm p.2 := by
      intro p
      have hinner : (∫ t, Real.exp (lam * Z (Function.update (Fin.insertNth k p.1 p.2) k t)) ∂(μ k))
          = ∫ s, gf p.2 s ∂(μ k) := by
        apply integral_congr_ae; filter_upwards with t
        rw [upd_insertNth k p.1 t p.2]
      rw [hinner, hBterm]
    -- rewrite integrand then prod-symm + inner const collapse
    rw [integral_congr_ae (g := fun p => Bterm p.2) (ae_of_all _ hBeq)]
    -- now ∫ p, Bterm p.2 ∂(μk ⊗ ν)  =  ∫ rest, Bterm rest ∂ν
    -- measurability of rest ↦ ∫ s, gf rest s
    have hgf_prod_meas : Measurable (fun q : (∀ j, α (k.succAbove j)) × α k =>
        gf q.1 q.2) := by
      have : Measurable (fun q : (∀ j, α (k.succAbove j)) × α k =>
          g (Fin.insertNth k q.2 q.1)) := by
        refine hgmeas.comp ?_
        apply measurable_pi_iff.2
        intro i
        rcases eq_or_ne i k with rfl | hik
        · simp only [Fin.insertNth_apply_same]; exact measurable_snd
        · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hik
          simp only [Fin.insertNth_apply_succAbove]
          exact (measurable_pi_apply j).comp measurable_fst
      exact this
    have hmint : Measurable (fun rest => ∫ s, gf rest s ∂(μ k)) := by
      apply StronglyMeasurable.measurable
      apply StronglyMeasurable.integral_prod_right (f := fun rest s => gf rest s)
      exact hgf_prod_meas.stronglyMeasurable
    have hBint : Integrable (fun p : α k × (∀ j, α (k.succAbove j)) => Bterm p.2)
        ((μ k).prod ν) := by
      refine hprodint _ (CC * (|Real.log cc| + |Real.log CC|)) ?_ (fun p => ?_)
      · rw [hBterm]
        exact ((hmint.comp measurable_snd).mul ((hmint.comp measurable_snd).log))
      · rw [hBterm, Real.norm_eq_abs, abs_mul]
        have hb1 : |∫ s, gf p.2 s ∂(μ k)| ≤ CC := by
          rw [abs_of_nonneg (le_trans (le_of_lt hcpos) (hmlb p.2))]; exact hmub p.2
        have hb2 : |Real.log (∫ s, gf p.2 s ∂(μ k))| ≤ |Real.log cc| + |Real.log CC| := by
          have hlo : Real.log cc ≤ Real.log (∫ s, gf p.2 s ∂(μ k)) :=
            Real.log_le_log hcpos (hmlb p.2)
          have hhi : Real.log (∫ s, gf p.2 s ∂(μ k)) ≤ Real.log CC :=
            Real.log_le_log (lt_of_lt_of_le hcpos (hmlb p.2)) (hmub p.2)
          rw [abs_le]
          constructor
          · linarith [neg_abs_le (Real.log cc), abs_nonneg (Real.log CC)]
          · linarith [le_abs_self (Real.log CC), abs_nonneg (Real.log cc)]
        apply mul_le_mul hb1 hb2 (abs_nonneg _) (le_of_lt hcCpos)
    rw [integral_prod_symm _ hBint]
    apply integral_congr_ae; filter_upwards with rest
    rw [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
  -- ===== combine =====
  rw [hA, hB, hC]
  -- integrability of Aterm, Bterm, Cterm over ν
  -- measurability of (rest,s) ↦ gf rest s as a prod fn (for integral_prod_right)
  have hgf_prod_meas2 : Measurable (fun q : (∀ j, α (k.succAbove j)) × α k => gf q.1 q.2) := by
    have : Measurable (fun q : (∀ j, α (k.succAbove j)) × α k =>
        g (Fin.insertNth k q.2 q.1)) := by
      refine hgmeas.comp ?_
      apply measurable_pi_iff.2
      intro i
      rcases eq_or_ne i k with rfl | hik
      · simp only [Fin.insertNth_apply_same]; exact measurable_snd
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hik
        simp only [Fin.insertNth_apply_succAbove]
        exact (measurable_pi_apply j).comp measurable_fst
    exact this
  have hAterm_meas : Measurable Aterm := by
    rw [hAterm]
    apply StronglyMeasurable.measurable
    apply StronglyMeasurable.integral_prod_right (f := fun rest s => gf rest s * Real.log (gf rest s))
    exact (hgf_prod_meas2.mul hgf_prod_meas2.log).stronglyMeasurable
  have hmint2 : Measurable (fun rest => ∫ s, gf rest s ∂(μ k)) := by
    apply StronglyMeasurable.measurable
    apply StronglyMeasurable.integral_prod_right (f := fun rest s => gf rest s)
    exact hgf_prod_meas2.stronglyMeasurable
  have hBterm_meas : Measurable Bterm := by
    rw [hBterm]; exact hmint2.mul hmint2.log
  have hCterm_meas : Measurable Cterm := by
    rw [hCterm]
    apply StronglyMeasurable.measurable
    apply StronglyMeasurable.integral_prod_right
      (f := fun rest s => gf rest s
        * (Real.exp (-(lam * (Z (Fin.insertNth k s rest) - Zk (Fin.insertNth k s rest))))
            - 1 + lam * (Z (Fin.insertNth k s rest) - Zk (Fin.insertNth k s rest))))
    refine (hgf_prod_meas2.mul ?_).stronglyMeasurable
    have hZp : Measurable (fun q : (∀ j, α (k.succAbove j)) × α k =>
        Z (Fin.insertNth k q.2 q.1)) := by
      refine hZmeas.comp ?_
      apply measurable_pi_iff.2; intro i
      rcases eq_or_ne i k with rfl | hik
      · simp only [Fin.insertNth_apply_same]; exact measurable_snd
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hik
        simp only [Fin.insertNth_apply_succAbove]; exact (measurable_pi_apply j).comp measurable_fst
    have hZkp : Measurable (fun q : (∀ j, α (k.succAbove j)) × α k =>
        Zk (Fin.insertNth k q.2 q.1)) := by
      refine hZkmeas.comp ?_
      apply measurable_pi_iff.2; intro i
      rcases eq_or_ne i k with rfl | hik
      · simp only [Fin.insertNth_apply_same]; exact measurable_snd
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hik
        simp only [Fin.insertNth_apply_succAbove]; exact (measurable_pi_apply j).comp measurable_fst
    exact (((hZp.sub hZkp).const_mul lam).neg.exp.sub measurable_const).add
      ((hZp.sub hZkp).const_mul lam)
  -- bounds on Aterm, Bterm, Cterm
  have hAterm_int : Integrable Aterm ν := by
    refine hint ν _ (CC * (|Real.log cc| + |Real.log CC|)) hAterm_meas (fun rest => ?_)
    rw [hAterm, Real.norm_eq_abs]
    have hbd := norm_integral_le_of_norm_le_const (μ := μ k)
      (f := fun s => gf rest s * Real.log (gf rest s))
      (C := CC * (|Real.log cc| + |Real.log CC|)) (ae_of_all _ (fun s => by
        rw [Real.norm_eq_abs, abs_mul]
        apply mul_le_mul (by rw [abs_of_nonneg (hgnn _)]; exact hgub _)
          (by rw [hlog_gf]; exact hlamZ_bd _) (abs_nonneg _) (le_of_lt hcCpos)))
    rw [measureReal_univ_eq_one, mul_one] at hbd
    rw [Real.norm_eq_abs] at hbd; exact hbd
  have hBterm_int : Integrable Bterm ν := by
    refine hint ν _ (CC * (|Real.log cc| + |Real.log CC|)) hBterm_meas (fun rest => ?_)
    rw [hBterm, Real.norm_eq_abs, abs_mul]
    have hb1 : |∫ s, gf rest s ∂(μ k)| ≤ CC := by
      rw [abs_of_nonneg (le_trans (le_of_lt hcpos) (hmlb rest))]; exact hmub rest
    have hb2 : |Real.log (∫ s, gf rest s ∂(μ k))| ≤ |Real.log cc| + |Real.log CC| := by
      have hlo : Real.log cc ≤ Real.log (∫ s, gf rest s ∂(μ k)) := Real.log_le_log hcpos (hmlb rest)
      have hhi : Real.log (∫ s, gf rest s ∂(μ k)) ≤ Real.log CC :=
        Real.log_le_log (lt_of_lt_of_le hcpos (hmlb rest)) (hmub rest)
      rw [abs_le]
      exact ⟨by linarith [neg_abs_le (Real.log cc), abs_nonneg (Real.log CC)],
        by linarith [le_abs_self (Real.log CC), abs_nonneg (Real.log cc)]⟩
    apply mul_le_mul hb1 hb2 (abs_nonneg _) (le_of_lt hcCpos)
  have hCterm_int : Integrable Cterm ν := by
    refine hint ν _ (CC * (Real.exp Du + 1 + Du)) hCterm_meas (fun rest => ?_)
    rw [hCterm, Real.norm_eq_abs]
    have hbd := norm_integral_le_of_norm_le_const (μ := μ k)
      (f := fun s => gf rest s
        * (Real.exp (-(lam * (Z (Fin.insertNth k s rest) - Zk (Fin.insertNth k s rest))))
            - 1 + lam * (Z (Fin.insertNth k s rest) - Zk (Fin.insertNth k s rest))))
      (C := CC * (Real.exp Du + 1 + Du)) (ae_of_all _ (fun s => by
        rw [Real.norm_eq_abs, abs_mul]
        apply mul_le_mul (by rw [abs_of_nonneg (hgnn _)]; exact hgub _) (hphibd _)
          (abs_nonneg _) (le_of_lt hcCpos)))
    rw [measureReal_univ_eq_one, mul_one] at hbd
    rw [Real.norm_eq_abs] at hbd; exact hbd
  -- finish: ∫ A - ∫ B = ∫ (A-B) ≤ ∫ C
  rw [← integral_sub hAterm_int hBterm_int]
  apply integral_mono (hAterm_int.sub hBterm_int) hCterm_int
  intro rest
  have := hfiber rest
  simp only [hAterm, hBterm, hCterm]
  exact this

/-! ### Main theorem: modified log-Sobolev inequality for the sup functional Z. -/

set_option maxHeartbeats 1600000 in
theorem solution
    {n : ℕ} {α : Fin n → Type} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : (∀ i, α i) → ℝ) (Zk : Fin n → (∀ i, α i) → ℝ) (lam : ℝ)
    (hZmeas : Measurable Z) (hZkmeas : ∀ k, Measurable (Zk k))
    (hZk_indep : ∀ k x t, Zk k (Function.update x k t) = Zk k x)
    (c C Dzk : ℝ) (hcpos : 0 < c)
    (hglb : ∀ x, c ≤ Real.exp (lam * Z x))
    (hgub : ∀ x, Real.exp (lam * Z x) ≤ C)
    (hZkbd : ∀ k x, |Zk k x| ≤ Dzk) :
    (∫ x, Real.exp (lam * Z x) * Real.log (Real.exp (lam * Z x)) ∂(Measure.pi μ)
      - (∫ x, Real.exp (lam * Z x) ∂(Measure.pi μ))
          * Real.log (∫ x, Real.exp (lam * Z x) ∂(Measure.pi μ)))
    ≤ ∑ k : Fin n, ∫ x, Real.exp (lam * Z x)
        * (Real.exp (-(lam * (Z x - Zk k x))) - 1 + lam * (Z x - Zk k x)) ∂(Measure.pi μ) := by
  classical
  -- g measurable
  have hgmeas : Measurable (fun x => Real.exp (lam * Z x)) := (hZmeas.const_mul lam).exp
  -- N-coordinate Han subadditivity (positivity-restricted), imported as the standalone reusable
  -- node `entropy_n_coordinate_han_subadditivity_measure_pi_pos` (proven by induction from the
  -- TRUE positivity-restricted 2-coordinate Han; replaces the false unconditional node 9bfe3e7e).
  -- `c ≤ g = exp(lam·Z)` supplies the required positivity.
  have hHan := entropy_n_coordinate_han_subadditivity_measure_pi_pos
      μ (fun x => Real.exp (lam * Z x)) c C hcpos hgmeas hglb hgub
  refine le_trans hHan ?_
  -- per-coordinate bound
  cases n with
  | zero => simp
  | succ m =>
    apply Finset.sum_le_sum
    intro k _
    exact per_coord_bound μ Z (Zk k) lam k hZmeas (hZkmeas k) (hZk_indep k) c C Dzk hcpos
      hglb hgub (hZkbd k)
