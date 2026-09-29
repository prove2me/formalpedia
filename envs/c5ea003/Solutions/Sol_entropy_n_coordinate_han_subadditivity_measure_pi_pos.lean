-- Prove2me | solution 1 for entropy_n_coordinate_han_subadditivity_measure_pi_pos
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-24T18:21:45.428551+00:00
-- url     : https://prove2.me/submissions/e1b570d5-6a4c-46d2-aa5d-b79e434e08d6

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_entropy_chain_rule_general_two_coordinate_han_subadditivity
import Theorems.Thm_entropy_convexity_refinement_marginal_le_integral_fiber
open Real MeasureTheory

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

/-- **Positive 2-coordinate Han subadditivity** (the TRUE, nonnegative-restricted form of the
2-coordinate Han inequality), proven sorry-free from the chain rule (CHILD 3) and the convexity
refinement (CHILD 4) with all their integrability hypotheses discharged from boundedness.
This is the statement CHILD 1's `H2` *should* require; CHILD 1's actual `H2` drops the
`cc ≤ F` positivity and is consequently false. -/
theorem han2_pos {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (ρ : Measure A) (σ : Measure B) [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ]
    (F : A × B → ℝ) (cc CC : ℝ) (hcpos : 0 < cc)
    (hFmeas : Measurable F) (hlb : ∀ p, cc ≤ F p) (hub : ∀ p, F p ≤ CC) :
    ((∫ p, F p * Real.log (F p) ∂(ρ.prod σ))
        - (∫ p, F p ∂(ρ.prod σ)) * Real.log (∫ p, F p ∂(ρ.prod σ)))
      ≤ (∫ y, ((∫ x, F (x, y) * Real.log (F (x, y)) ∂ρ)
            - (∫ x, F (x, y) ∂ρ) * Real.log (∫ x, F (x, y) ∂ρ)) ∂σ)
        + ∫ x, ((∫ y, F (x, y) * Real.log (F (x, y)) ∂σ)
            - (∫ y, F (x, y) ∂σ) * Real.log (∫ y, F (x, y) ∂σ)) ∂ρ := by
  haveI : IsProbabilityMeasure (ρ.prod σ) := by infer_instance
  have hFnn : ∀ p, 0 ≤ F p := fun p => le_trans (le_of_lt hcpos) (hlb p)
  have hFpos : ∀ p, 0 < F p := fun p => lt_of_lt_of_le hcpos (hlb p)
  have hAne : Nonempty A := by
    by_contra h; rw [not_nonempty_iff] at h
    have h0 : ρ Set.univ = 0 := by rw [Set.univ_eq_empty_iff.2 h]; simp
    have := (measure_univ (μ := ρ)); rw [h0] at this; exact one_ne_zero this.symm
  have hBne : Nonempty B := by
    by_contra h; rw [not_nonempty_iff] at h
    have h0 : σ Set.univ = 0 := by rw [Set.univ_eq_empty_iff.2 h]; simp
    have := (measure_univ (μ := σ)); rw [h0] at this; exact one_ne_zero this.symm
  have hCpos : 0 < CC := lt_of_lt_of_le hcpos (le_trans (hlb (hAne.some, hBne.some)) (hub _))
  set L : ℝ := |Real.log cc| + |Real.log CC| with hL
  have hFxmeas : ∀ x, Measurable (fun y => F (x, y)) := fun x => hFmeas.comp (measurable_prodMk_left)
  have hFymeas : ∀ y, Measurable (fun x => F (x, y)) := fun y => hFmeas.comp (measurable_prodMk_right)
  have hg1meas : Measurable (fun x => ∫ y, F (x, y) ∂σ) :=
    (hFmeas.stronglyMeasurable.integral_prod_right').measurable
  have hg2meas : Measurable (fun y => ∫ x, F (x, y) ∂ρ) := by
    have hsw : Measurable (fun q : B × A => F (q.2, q.1)) :=
      hFmeas.comp (measurable_snd.prodMk measurable_fst)
    exact (hsw.stronglyMeasurable.integral_prod_right').measurable
  have hF_int : Integrable F (ρ.prod σ) :=
    bdd_int _ F CC hFmeas (fun p => by rw [Real.norm_eq_abs, abs_of_nonneg (hFnn p)]; exact hub p)
  have hFlog_int : Integrable (fun p => F p * Real.log (F p)) (ρ.prod σ) :=
    bdd_int _ _ (CC * L) (hFmeas.mul hFmeas.log) (fun p => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (by rw [abs_of_nonneg (hFnn p)]; exact hub p) (log_bd hcpos (hlb p) (hub p))
        (abs_nonneg _) (le_of_lt hCpos))
  have hg1lb : ∀ x, cc ≤ ∫ y, F (x, y) ∂σ := fun x => by
    calc cc = ∫ _y, cc ∂σ := by rw [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
      _ ≤ _ := integral_mono (integrable_const _)
          (bdd_int _ _ CC (hFxmeas x) (fun y => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hFnn _)]; exact hub _)) (fun y => hlb _)
  have hg1ub : ∀ x, ∫ y, F (x, y) ∂σ ≤ CC := fun x => by
    calc ∫ y, F (x, y) ∂σ ≤ ∫ _y, CC ∂σ := integral_mono
          (bdd_int _ _ CC (hFxmeas x) (fun y => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hFnn _)]; exact hub _)) (integrable_const _)
          (fun y => hub _)
      _ = CC := by rw [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
  have hg2lb : ∀ y, cc ≤ ∫ x, F (x, y) ∂ρ := fun y => by
    calc cc = ∫ _x, cc ∂ρ := by rw [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
      _ ≤ _ := integral_mono (integrable_const _)
          (bdd_int _ _ CC (hFymeas y) (fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hFnn _)]; exact hub _)) (fun x => hlb _)
  have hg2ub : ∀ y, ∫ x, F (x, y) ∂ρ ≤ CC := fun y => by
    calc ∫ x, F (x, y) ∂ρ ≤ ∫ _x, CC ∂ρ := integral_mono
          (bdd_int _ _ CC (hFymeas y) (fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hFnn _)]; exact hub _)) (integrable_const _)
          (fun x => hub _)
      _ = CC := by rw [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
  have hg1log_int : Integrable (fun x => (∫ y, F (x, y) ∂σ) * Real.log (∫ y, F (x, y) ∂σ)) ρ :=
    bdd_int _ _ (CC * L) (hg1meas.mul hg1meas.log) (fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (by rw [abs_of_nonneg (le_trans (le_of_lt hcpos) (hg1lb x))]; exact hg1ub x)
        (log_bd hcpos (hg1lb x) (hg1ub x)) (abs_nonneg _) (le_of_lt hCpos))
  have hchain := entropy_chain_rule_general_two_coordinate_han_subadditivity
    (μ := ρ) (ν := σ) (f := F) hF_int hFlog_int hg1log_int
  have hm_int : Integrable (fun y => ∫ x, F (x, y) ∂ρ) σ :=
    bdd_int _ _ CC hg2meas (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_trans (le_of_lt hcpos) (hg2lb y))]; exact hg2ub y)
  have hfx_int : ∀ x, Integrable (fun y => F (x, y)) σ := fun x =>
    bdd_int _ _ CC (hFxmeas x) (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnn _)]; exact hub _)
  have hfx_logm_int : ∀ x, Integrable (fun y => F (x, y) * Real.log (∫ x', F (x', y) ∂ρ)) σ :=
    fun x => bdd_int _ _ (CC * L) ((hFxmeas x).mul (hg2meas.log)) (fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (by rw [abs_of_nonneg (hFnn _)]; exact hub _)
        (log_bd hcpos (hg2lb y) (hg2ub y)) (abs_nonneg _) (le_of_lt hCpos))
  have hfx_logf_int : ∀ x, Integrable (fun y => F (x, y) * Real.log (F (x, y))) σ :=
    fun x => bdd_int _ _ (CC * L) ((hFxmeas x).mul (hFxmeas x).log) (fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (by rw [abs_of_nonneg (hFnn _)]; exact hub _)
        (log_bd hcpos (hlb _) (hub _)) (abs_nonneg _) (le_of_lt hCpos))
  have h_inner_x_int : Integrable (fun x => ∫ y, (F (x, y) * Real.log (F (x, y))
      - F (x, y) * Real.log (∫ x', F (x', y) ∂ρ)) ∂σ) ρ := by
    refine bdd_int _ _ (2 * (CC * L)) ?_ (fun x => ?_)
    · have hh : Measurable (fun q : A × B => F q * Real.log (F q)
          - F q * Real.log (∫ x', F (x', q.2) ∂ρ)) :=
        (hFmeas.mul hFmeas.log).sub (hFmeas.mul ((hg2meas.comp measurable_snd).log))
      exact (hh.stronglyMeasurable.integral_prod_right').measurable
    · rw [Real.norm_eq_abs]
      have hbd := norm_integral_le_of_norm_le_const (μ := σ)
        (f := fun y => F (x, y) * Real.log (F (x, y)) - F (x, y) * Real.log (∫ x', F (x', y) ∂ρ))
        (C := 2 * (CC * L)) (ae_of_all _ (fun y => by
          rw [Real.norm_eq_abs]
          have e1 : |F (x, y) * Real.log (F (x, y)) - F (x, y) * Real.log (∫ x', F (x', y) ∂ρ)|
              ≤ |F (x, y) * Real.log (F (x, y))| + |F (x, y) * Real.log (∫ x', F (x', y) ∂ρ)| :=
            abs_sub _ _
          have b1 : |F (x, y) * Real.log (F (x, y))| ≤ CC * L := by
            rw [abs_mul]; exact mul_le_mul (by rw [abs_of_nonneg (hFnn _)]; exact hub _)
              (log_bd hcpos (hlb _) (hub _)) (abs_nonneg _) (le_of_lt hCpos)
          have b2 : |F (x, y) * Real.log (∫ x', F (x', y) ∂ρ)| ≤ CC * L := by
            rw [abs_mul]; exact mul_le_mul (by rw [abs_of_nonneg (hFnn _)]; exact hub _)
              (log_bd hcpos (hg2lb y) (hg2ub y)) (abs_nonneg _) (le_of_lt hCpos)
          linarith [e1, b1, b2]))
      rw [measureReal_univ_eq_one, mul_one, Real.norm_eq_abs] at hbd; exact hbd
  have hfm_prod_int : Integrable (fun p : A × B => F p * Real.log (∫ x', F (x', p.2) ∂ρ))
      (ρ.prod σ) :=
    bdd_int _ _ (CC * L) (hFmeas.mul ((hg2meas.comp measurable_snd).log)) (fun p => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (by rw [abs_of_nonneg (hFnn _)]; exact hub _)
        (log_bd hcpos (hg2lb p.2) (hg2ub p.2)) (abs_nonneg _) (le_of_lt hCpos))
  have hconv := entropy_convexity_refinement_marginal_le_integral_fiber
    (μ := ρ) (ν := σ) (f := F) hFpos hF_int hFlog_int hg1log_int hm_int hfx_int hfx_logm_int
    hfx_logf_int h_inner_x_int hfm_prod_int
  rw [hchain]
  exact add_le_add hconv (le_refl _)

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


private theorem insert_update_bridge {m : ℕ} {α : Fin (m+1) → Type}
    (a : α 0) (rest : ∀ j, α ((0 : Fin (m+1)).succAbove j)) (j : Fin m)
    (t : α ((0 : Fin (m+1)).succAbove j)) :
    Fin.insertNth 0 a (Function.update rest j t)
      = Function.update (Fin.insertNth 0 a rest) ((0 : Fin (m+1)).succAbove j) t := by
  ext i
  rcases eq_or_ne i ((0 : Fin (m+1)).succAbove j) with h | h
  · subst h
    rw [Function.update_self, Fin.insertNth_apply_succAbove, Function.update_self]
  · rw [Function.update_of_ne h]
    rcases eq_or_ne i 0 with h0 | h0
    · subst h0; simp [Fin.insertNth_apply_same]
    · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq h0
      rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
      have hjj' : j' ≠ j := by intro hc; subst hc; exact h rfl
      rw [Function.update_of_ne hjj']

set_option maxHeartbeats 3200000 in
theorem solution : ∀ {n : ℕ} {α : Fin n → Type} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (g : (∀ i, α i) → ℝ) (cc CC : ℝ), 0 < cc →
    Measurable g → (∀ x, cc ≤ g x) → (∀ x, g x ≤ CC) →
    ((∫ x, g x * Real.log (g x) ∂(Measure.pi μ))
        - (∫ x, g x ∂(Measure.pi μ)) * Real.log (∫ x, g x ∂(Measure.pi μ)))
      ≤ ∑ k : Fin n,
          ((∫ x, g x * Real.log (g x) ∂(Measure.pi μ))
            - ∫ x, (∫ t, g (Function.update x k t) ∂(μ k))
                * Real.log (∫ t, g (Function.update x k t) ∂(μ k)) ∂(Measure.pi μ)) := by
  intro n
  induction n with
  | zero =>
    intro α _ μ _ g cc CC hcpos hgmeas hglb hgub
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    have hsub : Subsingleton (∀ i : Fin 0, α i) := by
      constructor; intro x y; funext i; exact i.elim0
    have hne : Nonempty (∀ i : Fin 0, α i) := ⟨fun i => i.elim0⟩
    have hconst : ∀ x : (∀ i, α i), g x = g hne.some := by
      intro x; congr 1; exact Subsingleton.elim x hne.some
    have eGL : ∫ x, g x * Real.log (g x) ∂(Measure.pi μ)
        = g hne.some * Real.log (g hne.some) := by
      rw [show (fun x => g x * Real.log (g x))
          = (fun _ => g hne.some * Real.log (g hne.some)) from
        funext (fun x => by rw [hconst x])]
      rw [integral_const]; simp
    have eG : ∫ x, g x ∂(Measure.pi μ) = g hne.some := by
      rw [show (fun x => g x) = (fun _ => g hne.some) from funext (fun x => hconst x)]
      rw [integral_const]; simp
    rw [eGL, eG]; simp
  | succ m ih =>
    intro α _ μ _ g cc CC hcpos hgmeas hglb hgub
    classical
    set ν : Measure (∀ j, α ((0:Fin (m+1)).succAbove j)) :=
      Measure.pi (fun j => μ ((0:Fin (m+1)).succAbove j)) with hν
    haveI : IsProbabilityMeasure ν := by rw [hν]; infer_instance
    haveI : IsProbabilityMeasure (Measure.pi μ) := by infer_instance
    set L : ℝ := |Real.log cc| + |Real.log CC| with hL
    have hαne : ∀ i, Nonempty (α i) := by
      intro i
      by_contra h; rw [not_nonempty_iff] at h
      have h0 : (μ i) Set.univ = 0 := by rw [Set.univ_eq_empty_iff.2 h]; simp
      have := (measure_univ (μ := μ i)); rw [h0] at this; exact one_ne_zero this.symm
    have hpine : Nonempty (∀ i, α i) := ⟨fun i => (hαne i).some⟩
    have hCpos : 0 < CC := lt_of_lt_of_le hcpos (le_trans (hglb hpine.some) (hgub _))
    -- G p = g (insertNth 0 p.1 p.2)
    set G : α 0 × (∀ j, α ((0:Fin (m+1)).succAbove j)) → ℝ :=
      fun p => g (Fin.insertNth 0 p.1 p.2) with hG
    have hGmeas : Measurable G :=
      hgmeas.comp (MeasurableEquiv.piFinSuccAbove α 0).symm.measurable
    have hGlb : ∀ p, cc ≤ G p := fun p => hglb _
    have hGub : ∀ p, G p ≤ CC := fun p => hgub _
    have hGnn : ∀ p, 0 ≤ G p := fun p => le_of_lt (lt_of_lt_of_le hcpos (hGlb p))
    haveI : IsProbabilityMeasure ((μ 0).prod ν) := by infer_instance

    -- measurability of fiber functions
    have hGxmeas : ∀ a, Measurable (fun rest => G (a, rest)) := fun a =>
      hGmeas.comp (measurable_prodMk_left)
    have hGymeas : ∀ y, Measurable (fun a => G (a, y)) := fun y =>
      hGmeas.comp (measurable_prodMk_right)
    -- integrability of G, G log G on prod
    have hGint : Integrable G ((μ 0).prod ν) :=
      bdd_int _ G CC hGmeas (fun p => by rw [Real.norm_eq_abs, abs_of_nonneg (hGnn p)]; exact hGub p)
    have hGlogint : Integrable (fun p => G p * Real.log (G p)) ((μ 0).prod ν) :=
      bdd_int _ _ (CC * L) (hGmeas.mul hGmeas.log) (fun p => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (by rw [abs_of_nonneg (hGnn p)]; exact hGub p) (log_bd hcpos (hGlb p) (hGub p))
          (abs_nonneg _) (le_of_lt hCpos))
    -- marginal over μ0: m0 y = ∫ x G(x,y) dμ0
    have hm0meas : Measurable (fun y => ∫ a, G (a, y) ∂(μ 0)) := by
      have hsw : Measurable (fun q : (∀ j, α ((0:Fin (m+1)).succAbove j)) × α 0 => G (q.2, q.1)) :=
        hGmeas.comp (measurable_snd.prodMk measurable_fst)
      exact (hsw.stronglyMeasurable.integral_prod_right').measurable
    have hGafib_int : ∀ y, Integrable (fun a => G (a, y)) (μ 0) := fun y =>
      bdd_int _ _ CC (hGymeas y) (fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hGnn _)]; exact hGub _)
    have hm0lb : ∀ y, cc ≤ ∫ a, G (a, y) ∂(μ 0) := fun y => by
      calc cc = ∫ _a, cc ∂(μ 0) := by rw [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
        _ ≤ _ := integral_mono (integrable_const _) (hGafib_int y) (fun a => hGlb _)
    have hm0ub : ∀ y, ∫ a, G (a, y) ∂(μ 0) ≤ CC := fun y => by
      calc ∫ a, G (a, y) ∂(μ 0) ≤ ∫ _a, CC ∂(μ 0) :=
            integral_mono (hGafib_int y) (integrable_const _) (fun a => hGub _)
        _ = CC := by rw [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
    -- marginal over ν: mν a = ∫ y G(a,y) dν
    have hmνmeas : Measurable (fun a => ∫ rest, G (a, rest) ∂ν) :=
      (hGmeas.stronglyMeasurable.integral_prod_right').measurable
    have hGyfib_int : ∀ a, Integrable (fun rest => G (a, rest)) ν := fun a =>
      bdd_int _ _ CC (hGxmeas a) (fun rest => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hGnn _)]; exact hGub _)

    -- han2 application
    have h2 := han2_pos (μ 0) ν G cc CC hcpos hGmeas hGlb hGub
    -- (L): LHS entropy transports to Ent_prod(G)
    have hLgl : (∫ x, g x * Real.log (g x) ∂(Measure.pi μ))
        = ∫ p, G p * Real.log (G p) ∂((μ 0).prod ν) :=
      transport_at_k μ 0 (fun x => g x * Real.log (g x))
    have hLg : (∫ x, g x ∂(Measure.pi μ)) = ∫ p, G p ∂((μ 0).prod ν) :=
      transport_at_k μ 0 (fun x => g x)
    -- split goal sum: ∑_{Fin (m+1)} = (k=0) + ∑_{j:Fin m} (k = succAbove 0 j)
    rw [Fin.sum_univ_succAbove _ (0 : Fin (m+1))]
    -- (b) the conditional B_0 transports to the marginal-over-mu0 form
    have hB0 : (∫ x, (∫ t, g (Function.update x 0 t) ∂(μ 0))
          * Real.log (∫ t, g (Function.update x 0 t) ∂(μ 0)) ∂(Measure.pi μ))
        = ∫ y, (∫ a, G (a, y) ∂(μ 0)) * Real.log (∫ a, G (a, y) ∂(μ 0)) ∂ν := by
      rw [transport_at_k μ 0 (fun w => (∫ t, g (Function.update w 0 t) ∂(μ 0))
          * Real.log (∫ t, g (Function.update w 0 t) ∂(μ 0)))]
      -- the transported integrand depends only on p.2
      have heq : ∀ p : α 0 × (∀ j, α ((0:Fin (m+1)).succAbove j)),
          (∫ t, g (Function.update (Fin.insertNth 0 p.1 p.2) 0 t) ∂(μ 0))
            * Real.log (∫ t, g (Function.update (Fin.insertNth 0 p.1 p.2) 0 t) ∂(μ 0))
          = (∫ a, G (a, p.2) ∂(μ 0)) * Real.log (∫ a, G (a, p.2) ∂(μ 0)) := by
        intro p
        have hinner : (∫ t, g (Function.update (Fin.insertNth 0 p.1 p.2) 0 t) ∂(μ 0))
            = ∫ a, G (a, p.2) ∂(μ 0) := by
          apply integral_congr_ae; filter_upwards with t
          rw [upd_insertNth 0 p.1 t p.2]
        rw [hinner]
      rw [integral_congr_ae (ae_of_all _ heq)]
      -- now \int_p [f p.2] = \int_y f y (integrate out independent mu0 coord)
      rw [integral_prod _ ?_]
      · simp only []
        rw [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
      · -- integrability of (fun p => f p.2)
        refine bdd_int _ _ (CC * L) ?_ (fun p => ?_)
        · exact (hm0meas.comp measurable_snd).mul ((hm0meas.comp measurable_snd).log)
        · rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (by rw [abs_of_nonneg (le_trans (le_of_lt hcpos) (hm0lb p.2))]; exact hm0ub p.2)
            (log_bd hcpos (hm0lb p.2) (hm0ub p.2)) (abs_nonneg _) (le_of_lt hCpos)
    rw [hLgl, hLg]
    refine le_trans h2 (add_le_add (le_of_eq ?_) ?_)
    · -- Claim_T1 : T1 = Phi_0 = (int g log g) - B_0
      have hAint : Integrable (fun y => ∫ a, G (a, y) * Real.log (G (a, y)) ∂(μ 0)) ν := by
        refine bdd_int _ _ (CC * L) ?_ (fun y => ?_)
        · have : Measurable (fun q : (∀ j, α ((0:Fin (m+1)).succAbove j)) × α 0 =>
              G (q.2, q.1) * Real.log (G (q.2, q.1))) :=
            (hGmeas.comp (measurable_snd.prodMk measurable_fst)).mul
              ((hGmeas.comp (measurable_snd.prodMk measurable_fst)).log)
          exact (this.stronglyMeasurable.integral_prod_right').measurable
        · rw [Real.norm_eq_abs]
          have hbd := norm_integral_le_of_norm_le_const (μ := μ 0)
            (f := fun a => G (a, y) * Real.log (G (a, y))) (C := CC * L) (ae_of_all _ (fun a => by
              rw [Real.norm_eq_abs, abs_mul]
              exact mul_le_mul (by rw [abs_of_nonneg (hGnn _)]; exact hGub _)
                (log_bd hcpos (hGlb _) (hGub _)) (abs_nonneg _) (le_of_lt hCpos)))
          rw [measureReal_univ_eq_one, mul_one, Real.norm_eq_abs] at hbd; exact hbd
      have hBint : Integrable
          (fun y => (∫ a, G (a, y) ∂(μ 0)) * Real.log (∫ a, G (a, y) ∂(μ 0))) ν := by
        refine bdd_int _ _ (CC * L) (hm0meas.mul hm0meas.log) (fun y => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (by rw [abs_of_nonneg (le_trans (le_of_lt hcpos) (hm0lb y))]; exact hm0ub y)
          (log_bd hcpos (hm0lb y) (hm0ub y)) (abs_nonneg _) (le_of_lt hCpos)
      rw [integral_prod_symm _ hGlogint, hB0, ← integral_sub hAint hBint]
    · -- Claim_T2 : T2 ≤ sum
      set μ' : ∀ j, Measure (α ((0:Fin (m+1)).succAbove j)) :=
        fun j => μ ((0:Fin (m+1)).succAbove j) with hμ'
      -- pointwise IH bound for each a
      have hpoint : ∀ a : α 0,
          ((∫ rest, G (a, rest) * Real.log (G (a, rest)) ∂ν)
              - (∫ rest, G (a, rest) ∂ν) * Real.log (∫ rest, G (a, rest) ∂ν))
            ≤ ∑ i : Fin m,
                ((∫ rest, G (a, rest) * Real.log (G (a, rest)) ∂ν)
                  - ∫ rest, (∫ t, G (a, Function.update rest i t) ∂(μ' i))
                      * Real.log (∫ t, G (a, Function.update rest i t) ∂(μ' i)) ∂ν) := by
        intro a
        have := ih μ' (fun rest => G (a, rest)) cc CC hcpos (hGxmeas a)
          (fun rest => hGlb _) (fun rest => hGub _)
        rw [hν]
        exact this
      -- (a') the entropy-first-term integrates back to ∫ g log g ∂π
      have hglg_back : (∫ a, (∫ rest, G (a, rest) * Real.log (G (a, rest)) ∂ν) ∂(μ 0))
          = ∫ x, g x * Real.log (g x) ∂(Measure.pi μ) := by
        rw [hLgl, ← integral_prod _ hGlogint]
      -- (b') B_{succAbove 0 i} transports to the iterated marginal form
      have hBi : ∀ i : Fin m,
          (∫ x, (∫ t, g (Function.update x ((0:Fin (m+1)).succAbove i) t) ∂(μ ((0:Fin (m+1)).succAbove i)))
              * Real.log (∫ t, g (Function.update x ((0:Fin (m+1)).succAbove i) t) ∂(μ ((0:Fin (m+1)).succAbove i)))
              ∂(Measure.pi μ))
            = ∫ a, (∫ rest, (∫ t, G (a, Function.update rest i t) ∂(μ' i))
                * Real.log (∫ t, G (a, Function.update rest i t) ∂(μ' i)) ∂ν) ∂(μ 0) := by
        intro i
        rw [transport_at_k μ 0 (fun w => (∫ t, g (Function.update w ((0:Fin (m+1)).succAbove i) t)
            ∂(μ ((0:Fin (m+1)).succAbove i)))
            * Real.log (∫ t, g (Function.update w ((0:Fin (m+1)).succAbove i) t) ∂(μ ((0:Fin (m+1)).succAbove i))))]
        have heq : ∀ p : α 0 × (∀ j, α ((0:Fin (m+1)).succAbove j)),
            (∫ t, g (Function.update (Fin.insertNth 0 p.1 p.2) ((0:Fin (m+1)).succAbove i) t)
                ∂(μ ((0:Fin (m+1)).succAbove i)))
              * Real.log (∫ t, g (Function.update (Fin.insertNth 0 p.1 p.2) ((0:Fin (m+1)).succAbove i) t)
                ∂(μ ((0:Fin (m+1)).succAbove i)))
            = (∫ t, G (p.1, Function.update p.2 i t) ∂(μ' i))
                * Real.log (∫ t, G (p.1, Function.update p.2 i t) ∂(μ' i)) := by
          intro p
          have hinner : (∫ t, g (Function.update (Fin.insertNth 0 p.1 p.2) ((0:Fin (m+1)).succAbove i) t)
                ∂(μ ((0:Fin (m+1)).succAbove i)))
              = ∫ t, G (p.1, Function.update p.2 i t) ∂(μ' i) := by
            rw [hμ']
            apply integral_congr_ae; filter_upwards with t
            rw [← insert_update_bridge p.1 p.2 i t]
          rw [hinner]
        rw [integral_congr_ae (ae_of_all _ heq), integral_prod]
        -- integrability of the prod integrand
        refine bdd_int _ _ (CC * L) ?_ (fun p => ?_)
        · have hm'meas : Measurable (fun q : α 0 × (∀ j, α ((0:Fin (m+1)).succAbove j)) =>
              ∫ t, G (q.1, Function.update q.2 i t) ∂(μ' i)) := by
            have hcomp : Measurable (fun r : (α 0 × (∀ j, α ((0:Fin (m+1)).succAbove j))) × α ((0:Fin (m+1)).succAbove i) =>
                G (r.1.1, Function.update r.1.2 i r.2)) := by
              apply hGmeas.comp
              refine Measurable.prodMk (measurable_fst.comp measurable_fst) ?_
              exact measurable_update'.comp
                ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
            exact (hcomp.stronglyMeasurable.integral_prod_right').measurable
          exact hm'meas.mul hm'meas.log
        · -- bound on the marginal m·log m
          have hmi_fib_int : Integrable (fun t => G (p.1, Function.update p.2 i t)) (μ' i) := by
            refine bdd_int _ _ CC ?_ (fun t => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hGnn _)]; exact hGub _)
            exact hGmeas.comp (measurable_prodMk_left.comp (measurable_update _))
          have hmilb : cc ≤ ∫ t, G (p.1, Function.update p.2 i t) ∂(μ' i) := by
            calc cc = ∫ _t, cc ∂(μ' i) := by
                  rw [hμ']; rw [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
              _ ≤ _ := integral_mono (by rw [hμ']; exact integrable_const _) hmi_fib_int (fun t => hGlb _)
          have hmiub : (∫ t, G (p.1, Function.update p.2 i t) ∂(μ' i)) ≤ CC := by
            calc ∫ t, G (p.1, Function.update p.2 i t) ∂(μ' i)
                  ≤ ∫ _t, CC ∂(μ' i) :=
                  integral_mono hmi_fib_int (by rw [hμ']; exact integrable_const _) (fun t => hGub _)
              _ = CC := by rw [hμ']; rw [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (by rw [abs_of_nonneg (le_trans (le_of_lt hcpos) hmilb)]; exact hmiub)
            (log_bd hcpos hmilb hmiub) (abs_nonneg _) (le_of_lt hCpos)
      -- abbreviations Ai, Bi
      -- Ai a = ∫ rest, G(a,rest) log G(a,rest) dν
      have hAimeas : Measurable (fun a => ∫ rest, G (a, rest) * Real.log (G (a, rest)) ∂ν) :=
        ((hGmeas.mul hGmeas.log).stronglyMeasurable.integral_prod_right').measurable
      have hAi_bd : ∀ a, |∫ rest, G (a, rest) * Real.log (G (a, rest)) ∂ν| ≤ CC * L := by
        intro a
        have hbd := norm_integral_le_of_norm_le_const (μ := ν)
          (f := fun rest => G (a, rest) * Real.log (G (a, rest))) (C := CC * L) (ae_of_all _ (fun rest => by
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul (by rw [abs_of_nonneg (hGnn _)]; exact hGub _)
              (log_bd hcpos (hGlb _) (hGub _)) (abs_nonneg _) (le_of_lt hCpos)))
        rw [probReal_univ, mul_one, Real.norm_eq_abs] at hbd
        simpa using hbd
      have hAi_int : Integrable (fun a => ∫ rest, G (a, rest) * Real.log (G (a, rest)) ∂ν) (μ 0) :=
        bdd_int _ _ (CC * L) hAimeas (fun a => by rw [Real.norm_eq_abs]; exact hAi_bd a)
      -- mν a = ∫ y G(a,y) dν, with bounds
      have hmνlb : ∀ a, cc ≤ ∫ rest, G (a, rest) ∂ν := fun a => by
        calc cc = ∫ _rest, cc ∂ν := by rw [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
          _ ≤ _ := integral_mono (integrable_const _) (hGyfib_int a) (fun rest => hGlb _)
      have hmνub : ∀ a, ∫ rest, G (a, rest) ∂ν ≤ CC := fun a => by
        calc ∫ rest, G (a, rest) ∂ν ≤ ∫ _rest, CC ∂ν :=
              integral_mono (hGyfib_int a) (integrable_const _) (fun rest => hGub _)
          _ = CC := by rw [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
      have hMν_int : Integrable
          (fun a => (∫ rest, G (a, rest) ∂ν) * Real.log (∫ rest, G (a, rest) ∂ν)) (μ 0) :=
        bdd_int _ _ (CC * L) (hmνmeas.mul hmνmeas.log) (fun a => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (by rw [abs_of_nonneg (le_trans (le_of_lt hcpos) (hmνlb a))]; exact hmνub a)
            (log_bd hcpos (hmνlb a) (hmνub a)) (abs_nonneg _) (le_of_lt hCpos))
      -- Bi i : marginal bounds for the inner ∫ t G(a, update rest i t) dμ'i
      have hMilb : ∀ i a rest, cc ≤ ∫ t, G (a, Function.update rest i t) ∂(μ' i) := by
        intro i a rest
        have hint : Integrable (fun t => G (a, Function.update rest i t)) (μ' i) :=
          bdd_int _ _ CC (hGmeas.comp (measurable_prodMk_left.comp (measurable_update _)))
            (fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hGnn _)]; exact hGub _)
        calc cc = ∫ _t, cc ∂(μ' i) := by
              rw [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
          _ ≤ _ := integral_mono (integrable_const _) hint (fun t => hGlb _)
      have hMiub : ∀ i a rest, (∫ t, G (a, Function.update rest i t) ∂(μ' i)) ≤ CC := by
        intro i a rest
        have hint : Integrable (fun t => G (a, Function.update rest i t)) (μ' i) :=
          bdd_int _ _ CC (hGmeas.comp (measurable_prodMk_left.comp (measurable_update _)))
            (fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hGnn _)]; exact hGub _)
        calc ∫ t, G (a, Function.update rest i t) ∂(μ' i) ≤ ∫ _t, CC ∂(μ' i) :=
              integral_mono hint (integrable_const _) (fun t => hGub _)
          _ = CC := by rw [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
      -- measurability of Bi i over μ0
      have hμ'prob : ∀ i, IsProbabilityMeasure (μ' i) := fun i => by rw [hμ']; infer_instance
      have hBimeas : ∀ i, Measurable (fun a => ∫ rest, (∫ t, G (a, Function.update rest i t) ∂(μ' i))
          * Real.log (∫ t, G (a, Function.update rest i t) ∂(μ' i)) ∂ν) := by
        intro i
        haveI := hμ'prob i
        have hg2 : Measurable (fun r : α 0 × (∀ j, α ((0:Fin (m+1)).succAbove j)) =>
            (∫ t, G (r.1, Function.update r.2 i t) ∂(μ' i))
              * Real.log (∫ t, G (r.1, Function.update r.2 i t) ∂(μ' i))) := by
          have hcomp : Measurable (fun s : (α 0 × (∀ j, α ((0:Fin (m+1)).succAbove j))) × α ((0:Fin (m+1)).succAbove i) =>
              G (s.1.1, Function.update s.1.2 i s.2)) := by
            apply hGmeas.comp
            refine Measurable.prodMk (measurable_fst.comp measurable_fst) ?_
            exact measurable_update'.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
          have hm := (hcomp.stronglyMeasurable.integral_prod_right' (ν := μ' i)).measurable
          exact hm.mul hm.log
        exact (hg2.stronglyMeasurable.integral_prod_right').measurable
      have hBi_int : ∀ i, Integrable (fun a => ∫ rest, (∫ t, G (a, Function.update rest i t) ∂(μ' i))
          * Real.log (∫ t, G (a, Function.update rest i t) ∂(μ' i)) ∂ν) (μ 0) := by
        intro i
        refine bdd_int _ _ (CC * L) (hBimeas i) (fun a => ?_)
        rw [Real.norm_eq_abs]
        have hbd := norm_integral_le_of_norm_le_const (μ := ν)
          (f := fun rest => (∫ t, G (a, Function.update rest i t) ∂(μ' i))
            * Real.log (∫ t, G (a, Function.update rest i t) ∂(μ' i))) (C := CC * L)
          (ae_of_all _ (fun rest => by
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul
              (by rw [abs_of_nonneg (le_trans (le_of_lt hcpos) (hMilb i a rest))]; exact hMiub i a rest)
              (log_bd hcpos (hMilb i a rest) (hMiub i a rest)) (abs_nonneg _) (le_of_lt hCpos)))
        rw [probReal_univ, mul_one, Real.norm_eq_abs] at hbd
        simpa using hbd
      -- per-i equality: ∫_a Ψ_i(a) dμ0 = (∫ G log G ∂prod) - B_{succAbove 0 i}
      have hPsiEq : ∀ i : Fin m,
          (∫ a, ((∫ rest, G (a, rest) * Real.log (G (a, rest)) ∂ν)
              - ∫ rest, (∫ t, G (a, Function.update rest i t) ∂(μ' i))
                  * Real.log (∫ t, G (a, Function.update rest i t) ∂(μ' i)) ∂ν) ∂(μ 0))
            = (∫ p, G p * Real.log (G p) ∂((μ 0).prod ν))
              - ∫ x, (∫ t, g (Function.update x ((0:Fin (m+1)).succAbove i) t) ∂(μ ((0:Fin (m+1)).succAbove i)))
                  * Real.log (∫ t, g (Function.update x ((0:Fin (m+1)).succAbove i) t)
                      ∂(μ ((0:Fin (m+1)).succAbove i))) ∂(Measure.pi μ) := by
        intro i
        rw [integral_sub hAi_int (hBi_int i), ← integral_prod _ hGlogint, hBi i]
      -- bound T2 by ∑ via integral_mono + hpoint
      have hsumint : Integrable (fun a => ∑ i : Fin m,
          ((∫ rest, G (a, rest) * Real.log (G (a, rest)) ∂ν)
            - ∫ rest, (∫ t, G (a, Function.update rest i t) ∂(μ' i))
                * Real.log (∫ t, G (a, Function.update rest i t) ∂(μ' i)) ∂ν)) (μ 0) := by
        apply integrable_finset_sum
        intro i _
        exact (hAi_int).sub (hBi_int i)
      have hT2int : Integrable (fun a => (∫ rest, G (a, rest) * Real.log (G (a, rest)) ∂ν)
          - (∫ rest, G (a, rest) ∂ν) * Real.log (∫ rest, G (a, rest) ∂ν)) (μ 0) :=
        hAi_int.sub hMν_int
      calc (∫ a, ((∫ rest, G (a, rest) * Real.log (G (a, rest)) ∂ν)
              - (∫ rest, G (a, rest) ∂ν) * Real.log (∫ rest, G (a, rest) ∂ν)) ∂(μ 0))
          ≤ ∫ a, (∑ i : Fin m,
              ((∫ rest, G (a, rest) * Real.log (G (a, rest)) ∂ν)
                - ∫ rest, (∫ t, G (a, Function.update rest i t) ∂(μ' i))
                    * Real.log (∫ t, G (a, Function.update rest i t) ∂(μ' i)) ∂ν)) ∂(μ 0) :=
            integral_mono hT2int hsumint (fun a => hpoint a)
        _ = ∑ i : Fin m, ∫ a, ((∫ rest, G (a, rest) * Real.log (G (a, rest)) ∂ν)
                - ∫ rest, (∫ t, G (a, Function.update rest i t) ∂(μ' i))
                    * Real.log (∫ t, G (a, Function.update rest i t) ∂(μ' i)) ∂ν) ∂(μ 0) :=
            integral_finset_sum _ (fun i _ => (hAi_int).sub (hBi_int i))
        _ = _ := Finset.sum_congr rfl (fun i _ => hPsiEq i)
