-- Prove2me | solution 1 for entropy_n_coordinate_han_subadditivity_measure_pi
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-24T16:23:33.996954+00:00
-- url     : https://prove2.me/submissions/146681ba-31f2-4e2b-a79d-9f3e6ae99486

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.Pi

open Real MeasureTheory

/-- **n-coordinate Han subadditivity (entropy tensorization) over `Measure.pi` (`Fin n`).**

Self-contained single-theorem form: all helper lemmas (the bounded-positive integrability
toolkit, the coordinate-peeling transport, the per-coordinate summand identifications) are
inlined as `have`s inside the proof, and the `n`-induction is carried by an internal
`have key`.  `Ent` and `summand` are written out in raw form throughout. -/
theorem solution
    (H2 : ∀ {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
      (ρ : Measure A) (σ : Measure B) [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ]
      (F : A × B → ℝ),
      ((∫ p, F p * Real.log (F p) ∂(ρ.prod σ))
          - (∫ p, F p ∂(ρ.prod σ)) * Real.log (∫ p, F p ∂(ρ.prod σ)))
        ≤ (∫ y, ((∫ x, F (x, y) * Real.log (F (x, y)) ∂ρ)
              - (∫ x, F (x, y) ∂ρ) * Real.log (∫ x, F (x, y) ∂ρ)) ∂σ)
          + ∫ x, ((∫ y, F (x, y) * Real.log (F (x, y)) ∂σ)
              - (∫ y, F (x, y) ∂σ) * Real.log (∫ y, F (x, y) ∂σ)) ∂ρ)
    {n : ℕ} {α : Fin n → Type} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    {g : (∀ i, α i) → ℝ} {c C : ℝ}
    (hmeas : Measurable g) (hcpos : 0 < c) (hlb : ∀ x, c ≤ g x) (hub : ∀ x, g x ≤ C) :
    ((∫ x, g x * Real.log (g x) ∂(Measure.pi μ))
        - (∫ x, g x ∂(Measure.pi μ)) * Real.log (∫ x, g x ∂(Measure.pi μ)))
      ≤ ∑ k : Fin n,
          ((∫ x, g x * Real.log (g x) ∂(Measure.pi μ))
            - ∫ x, (∫ t, g (Function.update x k t) ∂(μ k))
                * Real.log (∫ t, g (Function.update x k t) ∂(μ k)) ∂(Measure.pi μ)) := by
  ----------------------------------------------------------------------------
  -- INTEGRABILITY TOOLKIT (HanInt + BddPos as a 4-fold conjunction)
  ----------------------------------------------------------------------------
  -- A measurable function with `|g| ≤ D` is integrable on a finite measure.
  have integrable_of_abs_bdd : ∀ {α : Type} [MeasurableSpace α] {μ : Measure α}
      [IsFiniteMeasure μ] {g : α → ℝ}, Measurable g → ∀ {D : ℝ}, (∀ x, |g x| ≤ D) →
      Integrable g μ := by
    intro α _ μ _ g hg D hbdd
    refine Integrable.mono' (integrable_const D) hg.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hbdd x)
  -- `|z·log z| ≤ C·L` whenever `c ≤ z ≤ C`, `0 < c`, and `L` bounds `|log c|,|log C|`.
  have abs_mul_log_bdd : ∀ {z c C L : ℝ}, 0 < c → c ≤ z → z ≤ C →
      |Real.log c| ≤ L → |Real.log C| ≤ L → |z * Real.log z| ≤ C * L := by
    intro z c C L hc hcz hzC hLc hLC
    have hz : 0 < z := lt_of_lt_of_le hc hcz
    rw [abs_mul]
    have h1 : |z| ≤ C := by rw [abs_of_pos hz]; exact hzC
    have h2 : |Real.log z| ≤ L := by
      rcases le_or_gt 1 z with h | h
      · have hle : Real.log z ≤ Real.log C := Real.log_le_log hz hzC
        have hlogz_nonneg : 0 ≤ Real.log z := Real.log_nonneg h
        rw [abs_of_nonneg hlogz_nonneg]
        calc Real.log z ≤ Real.log C := hle
          _ ≤ |Real.log C| := le_abs_self _
          _ ≤ L := hLC
      · have hlogz_neg : Real.log z ≤ 0 := Real.log_nonpos hz.le h.le
        rw [abs_of_nonpos hlogz_neg]
        have hzc : Real.log c ≤ Real.log z := Real.log_le_log hc hcz
        have : -Real.log z ≤ -Real.log c := by linarith
        calc -Real.log z ≤ -Real.log c := this
          _ ≤ |Real.log c| := neg_le_abs _
          _ ≤ L := hLc
    exact mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
  -- bounded-positive ⟹ integrable on a probability measure.
  have bp_integrable : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] {g : Ω → ℝ} {c C : ℝ},
      Measurable g → 0 < c → (∀ x, c ≤ g x) → (∀ x, g x ≤ C) → Integrable g μ := by
    intro Ω _ μ _ g c C hmeas hcpos hlb hub
    refine integrable_of_abs_bdd hmeas (D := max |c| |C|) (fun x => ?_)
    rw [abs_le]
    refine ⟨le_trans (by rw [neg_le]; exact le_trans (neg_le_abs c) (le_max_left _ _)) (hlb _),
      le_trans (hub _) (le_max_of_le_right (le_abs_self C))⟩
  -- bounded-positive ⟹ g·log g integrable on a probability measure.
  have bp_integrable_mul_log : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] {g : Ω → ℝ} {c C : ℝ},
      Measurable g → 0 < c → (∀ x, c ≤ g x) → (∀ x, g x ≤ C) →
      Integrable (fun x => g x * Real.log (g x)) μ := by
    intro Ω _ μ _ g c C hmeas hcpos hlb hub
    refine integrable_of_abs_bdd (hmeas.mul hmeas.log)
      (D := C * max |Real.log c| |Real.log C|) (fun x => ?_)
    exact abs_mul_log_bdd hcpos (hlb x) (hub x) (le_max_left _ _) (le_max_right _ _)
  ----------------------------------------------------------------------------
  -- The marginal `gₖ x = ∫ t, g(update x k t) dμₖ` is bounded-positive measurable.
  ----------------------------------------------------------------------------
  have bddPos_marginal : ∀ {m : ℕ} {β : Fin m → Type} [∀ i, MeasurableSpace (β i)]
      (μ : ∀ i, Measure (β i)) [∀ i, IsProbabilityMeasure (μ i)]
      {g : (∀ i, β i) → ℝ} {c C : ℝ},
      Measurable g → 0 < c → (∀ x, c ≤ g x) → (∀ x, g x ≤ C) → ∀ (k : Fin m),
      Measurable (fun x => ∫ t, g (Function.update x k t) ∂(μ k)) ∧
        (∀ x, c ≤ ∫ t, g (Function.update x k t) ∂(μ k)) ∧
        (∀ x, (∫ t, g (Function.update x k t) ∂(μ k)) ≤ C) := by
    intro m β _ μ _ g c C hmeas hcpos hlb hub k
    refine ⟨?_, ?_, ?_⟩
    · have hcurry : StronglyMeasurable
          (Function.uncurry (fun (x : ∀ i, β i) (t : β k) => g (Function.update x k t))) :=
        (hmeas.comp measurable_update').stronglyMeasurable
      exact (StronglyMeasurable.integral_prod_right (ν := μ k) hcurry).measurable
    · intro x
      have hint : Integrable (fun t => g (Function.update x k t)) (μ k) :=
        bp_integrable (hmeas.comp (measurable_update x)) hcpos
          (fun t => hlb _) (fun t => hub _)
      calc c = ∫ _ : β k, c ∂(μ k) := by rw [integral_const]; simp
        _ ≤ _ := integral_mono (integrable_const c) hint (fun t => hlb _)
    · intro x
      have hint : Integrable (fun t => g (Function.update x k t)) (μ k) :=
        bp_integrable (hmeas.comp (measurable_update x)) hcpos
          (fun t => hlb _) (fun t => hub _)
      calc (∫ t, g (Function.update x k t) ∂(μ k)) ≤ ∫ _ : β k, C ∂(μ k) :=
            integral_mono hint (integrable_const C) (fun t => hub _)
        _ = C := by rw [integral_const]; simp
  ----------------------------------------------------------------------------
  -- `(p : β 0 × Π rest) ↦ Fin.cons p.1 p.2` is measurable.
  ----------------------------------------------------------------------------
  have measurable_cons : ∀ {m : ℕ} {β : Fin (m+1) → Type} [∀ i, MeasurableSpace (β i)],
      Measurable (fun p : β 0 × (∀ j : Fin m, β (Fin.succ j)) =>
        (Fin.cons p.1 p.2 : ∀ i, β i)) := by
    intro m β _
    rw [measurable_pi_iff]
    intro i
    refine Fin.cases ?_ ?_ i
    · simp only [Fin.cons_zero]; exact measurable_fst
    · intro j; simp only [Fin.cons_succ]; exact (measurable_pi_apply j).comp measurable_snd
  ----------------------------------------------------------------------------
  -- The pushforward `F = g ∘ cons` is bounded-positive on the product.
  ----------------------------------------------------------------------------
  have bddPos_cons : ∀ {m : ℕ} {β : Fin (m+1) → Type} [∀ i, MeasurableSpace (β i)]
      {g : (∀ i, β i) → ℝ} {c C : ℝ},
      Measurable g → 0 < c → (∀ x, c ≤ g x) → (∀ x, g x ≤ C) →
      Measurable (fun p : β 0 × (∀ j : Fin m, β (Fin.succ j)) => g (Fin.cons p.1 p.2)) ∧
        (∀ p : β 0 × (∀ j : Fin m, β (Fin.succ j)), c ≤ g (Fin.cons p.1 p.2)) ∧
        (∀ p : β 0 × (∀ j : Fin m, β (Fin.succ j)), g (Fin.cons p.1 p.2) ≤ C) := by
    intro m β _ g c C hmeas hcpos hlb hub
    exact ⟨hmeas.comp measurable_cons, fun p => hlb _, fun p => hub _⟩
  ----------------------------------------------------------------------------
  -- Marginal over the first product coordinate of a bdd-pos function is bdd-pos.
  ----------------------------------------------------------------------------
  have bddPos_integral_fst : ∀ {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
      (ρ : Measure A) [IsProbabilityMeasure ρ] {F : A × B → ℝ} {c C : ℝ},
      Measurable F → 0 < c → (∀ p, c ≤ F p) → (∀ p, F p ≤ C) →
      Measurable (fun y => ∫ x, F (x, y) ∂ρ) ∧
        (∀ y, c ≤ ∫ x, F (x, y) ∂ρ) ∧ (∀ y, (∫ x, F (x, y) ∂ρ) ≤ C) := by
    intro A B _ _ ρ _ F c C hmeas hcpos hlb hub
    refine ⟨(StronglyMeasurable.integral_prod_left' (μ := ρ) hmeas.stronglyMeasurable).measurable,
      ?_, ?_⟩
    · intro y
      have hint : Integrable (fun x => F (x, y)) ρ :=
        bp_integrable (hmeas.comp (measurable_id.prodMk measurable_const)) hcpos
          (fun x => hlb _) (fun x => hub _)
      calc c = ∫ _ : A, c ∂ρ := by rw [integral_const]; simp
        _ ≤ _ := integral_mono (integrable_const c) hint (fun x => hlb _)
    · intro y
      have hint : Integrable (fun x => F (x, y)) ρ :=
        bp_integrable (hmeas.comp (measurable_id.prodMk measurable_const)) hcpos
          (fun x => hlb _) (fun x => hub _)
      calc (∫ x, F (x, y) ∂ρ) ≤ ∫ _ : A, C ∂ρ :=
            integral_mono hint (integrable_const C) (fun x => hub _)
        _ = C := by rw [integral_const]; simp
  ----------------------------------------------------------------------------
  -- Marginal over the second product coordinate of a bdd-pos function is bdd-pos.
  ----------------------------------------------------------------------------
  have bddPos_integral_snd : ∀ {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
      (σ : Measure B) [IsProbabilityMeasure σ] {F : A × B → ℝ} {c C : ℝ},
      Measurable F → 0 < c → (∀ p, c ≤ F p) → (∀ p, F p ≤ C) →
      Measurable (fun x => ∫ y, F (x, y) ∂σ) ∧
        (∀ x, c ≤ ∫ y, F (x, y) ∂σ) ∧ (∀ x, (∫ y, F (x, y) ∂σ) ≤ C) := by
    intro A B _ _ σ _ F c C hmeas hcpos hlb hub
    refine ⟨(StronglyMeasurable.integral_prod_right' (ν := σ) hmeas.stronglyMeasurable).measurable,
      ?_, ?_⟩
    · intro x
      have hint : Integrable (fun y => F (x, y)) σ :=
        bp_integrable (hmeas.comp (measurable_const.prodMk measurable_id)) hcpos
          (fun y => hlb _) (fun y => hub _)
      calc c = ∫ _ : B, c ∂σ := by rw [integral_const]; simp
        _ ≤ _ := integral_mono (integrable_const c) hint (fun y => hlb _)
    · intro x
      have hint : Integrable (fun y => F (x, y)) σ :=
        bp_integrable (hmeas.comp (measurable_const.prodMk measurable_id)) hcpos
          (fun y => hlb _) (fun y => hub _)
      calc (∫ y, F (x, y) ∂σ) ≤ ∫ _ : B, C ∂σ :=
            integral_mono hint (integrable_const C) (fun y => hub _)
        _ = C := by rw [integral_const]; simp
  ----------------------------------------------------------------------------
  -- The fundamental coordinate-peeling transport.
  ----------------------------------------------------------------------------
  have integral_pi_eq_prod_cons : ∀ {m : ℕ} {β : Fin (m+1) → Type} [∀ i, MeasurableSpace (β i)]
      (μ : ∀ i, Measure (β i)) [∀ i, IsProbabilityMeasure (μ i)] (h : (∀ i, β i) → ℝ),
      (∫ x, h x ∂(Measure.pi μ))
        = ∫ p : β 0 × (∀ j : Fin m, β (Fin.succ j)),
            h (Fin.cons p.1 p.2) ∂((μ 0).prod (Measure.pi (fun j => μ (Fin.succ j)))) := by
    intro m β _ μ _ h
    rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).integral_comp']
    simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq]
    rfl
  ----------------------------------------------------------------------------
  -- The MAIN induction (statement uses raw `Ent`/`summand` bodies).
  ----------------------------------------------------------------------------
  have key : ∀ (m : ℕ) {β : Fin m → Type} [∀ i, MeasurableSpace (β i)]
      (μ : ∀ i, Measure (β i)) [∀ i, IsProbabilityMeasure (μ i)]
      {g : (∀ i, β i) → ℝ} {c C : ℝ},
      Measurable g → 0 < c → (∀ x, c ≤ g x) → (∀ x, g x ≤ C) →
      ((∫ x, g x * Real.log (g x) ∂(Measure.pi μ))
          - (∫ x, g x ∂(Measure.pi μ)) * Real.log (∫ x, g x ∂(Measure.pi μ)))
        ≤ ∑ k : Fin m,
            ((∫ x, g x * Real.log (g x) ∂(Measure.pi μ))
              - ∫ x, (∫ t, g (Function.update x k t) ∂(μ k))
                  * Real.log (∫ t, g (Function.update x k t) ∂(μ k)) ∂(Measure.pi μ)) := by
    intro m
    induction m with
    | zero =>
      intro β _ μ _ g c C hmeas hcpos hlb hub
      rw [Fin.sum_univ_zero]
      rw [integral_unique, integral_unique]; simp [probReal_univ]
    | succ m ih =>
      intro β _ μ _ g c C hmeas hcpos hlb hub
      set Q := Measure.pi (fun j => μ (Fin.succ j)) with hQ
      set ρ := μ 0 with hρ
      set F : β 0 × (∀ j : Fin m, β (Fin.succ j)) → ℝ := fun p => g (Fin.cons p.1 p.2) with hFdef
      obtain ⟨hFmeas, hFlb, hFub⟩ := bddPos_cons hmeas hcpos hlb hub
      -- Ent over pi = Ent over the product, via cons-transport.
      have hEnt : ((∫ x, g x * Real.log (g x) ∂(Measure.pi μ))
            - (∫ x, g x ∂(Measure.pi μ)) * Real.log (∫ x, g x ∂(Measure.pi μ)))
          = ((∫ p, F p * Real.log (F p) ∂(ρ.prod Q))
            - (∫ p, F p ∂(ρ.prod Q)) * Real.log (∫ p, F p ∂(ρ.prod Q))) := by
        rw [integral_pi_eq_prod_cons μ (fun x => g x * Real.log (g x)),
            integral_pi_eq_prod_cons μ g]
      rw [hEnt]
      refine le_trans (H2 ρ Q F) ?_
      -- COLUMN term = summand 0.
      have hCol : (∫ y, ((∫ x, F (x, y) * Real.log (F (x, y)) ∂ρ)
              - (∫ x, F (x, y) ∂ρ) * Real.log (∫ x, F (x, y) ∂ρ)) ∂Q)
          = ((∫ x, g x * Real.log (g x) ∂(Measure.pi μ))
              - ∫ x, (∫ t, g (Function.update x 0 t) ∂(μ 0))
                  * Real.log (∫ t, g (Function.update x 0 t) ∂(μ 0)) ∂(Measure.pi μ)) := by
        have hFll : Integrable
            (fun p : β 0 × (∀ j, β (Fin.succ j)) =>
              g (Fin.cons p.1 p.2) * Real.log (g (Fin.cons p.1 p.2))) (ρ.prod Q) :=
          bp_integrable_mul_log (μ := ρ.prod Q) hFmeas hcpos hFlb hFub
        set M : (∀ j, β (Fin.succ j)) → ℝ := fun y => ∫ x, g (Fin.cons x y) ∂ρ with hMdef
        obtain ⟨hMmeas, hMlb, hMub⟩ := bddPos_integral_fst ρ hFmeas hcpos hFlb hFub
        rw [integral_pi_eq_prod_cons μ (fun x => g x * Real.log (g x))]
        rw [integral_pi_eq_prod_cons μ (fun x => (∫ t, g (Function.update x 0 t) ∂(μ 0))
              * Real.log (∫ t, g (Function.update x 0 t) ∂(μ 0)))]
        rw [integral_prod_symm _ hFll]
        have hterm2 : (∫ p : β 0 × (∀ j, β (Fin.succ j)),
              (∫ t, g (Function.update (Fin.cons p.1 p.2) 0 t) ∂(μ 0))
                * Real.log (∫ t, g (Function.update (Fin.cons p.1 p.2) 0 t) ∂(μ 0)) ∂(ρ.prod Q))
            = ∫ y, M y * Real.log (M y) ∂Q := by
          have hcongr : ∀ p : β 0 × (∀ j, β (Fin.succ j)),
              (∫ t, g (Function.update (Fin.cons p.1 p.2) 0 t) ∂(μ 0))
                * Real.log (∫ t, g (Function.update (Fin.cons p.1 p.2) 0 t) ∂(μ 0))
              = M p.2 * Real.log (M p.2) := by
            intro p
            have hinner : (∫ t, g (Function.update (Fin.cons p.1 p.2) 0 t) ∂(μ 0)) = M p.2 := by
              rw [hMdef]; apply integral_congr_ae; filter_upwards with t; rw [Fin.update_cons_zero]
            rw [hinner]
          rw [integral_congr_ae (Filter.Eventually.of_forall hcongr)]
          rw [integral_prod_symm (fun p => M p.2 * Real.log (M p.2))
            (bp_integrable_mul_log (μ := ρ.prod Q) (hMmeas.comp measurable_snd) hcpos
              (fun p => hMlb _) (fun p => hMub _))]
          simp_rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
        rw [hterm2, ← integral_sub hFll.integral_prod_right
          (bp_integrable_mul_log (μ := Q) hMmeas hcpos hMlb hMub)]
      -- ROW term ≤ ∑ over successors, via the induction hypothesis.
      have hRow_le : (∫ x, ((∫ y, F (x, y) * Real.log (F (x, y)) ∂Q)
              - (∫ y, F (x, y) ∂Q) * Real.log (∫ y, F (x, y) ∂Q)) ∂ρ)
          ≤ ∑ j : Fin m,
              ((∫ x, g x * Real.log (g x) ∂(Measure.pi μ))
                - ∫ x, (∫ t, g (Function.update x (Fin.succ j) t) ∂(μ (Fin.succ j)))
                    * Real.log (∫ t, g (Function.update x (Fin.succ j) t) ∂(μ (Fin.succ j)))
                  ∂(Measure.pi μ)) := by
        -- abbreviation for the j-th tail summand of the fibre function.
        -- summand_succ_eq: integrating the fibre summand in x recovers the (succ j) summand of g.
        have summand_succ_eq : ∀ (j : Fin m),
            (∫ x, ((∫ y, g (Fin.cons x y) * Real.log (g (Fin.cons x y))
                    ∂(Measure.pi (fun j => μ (Fin.succ j))))
                - ∫ y, (∫ t, g (Fin.cons x (Function.update y j t)) ∂(μ (Fin.succ j)))
                      * Real.log (∫ t, g (Fin.cons x (Function.update y j t)) ∂(μ (Fin.succ j)))
                    ∂(Measure.pi (fun j => μ (Fin.succ j)))) ∂(μ 0))
              = ((∫ x, g x * Real.log (g x) ∂(Measure.pi μ))
                - ∫ x, (∫ t, g (Function.update x (Fin.succ j) t) ∂(μ (Fin.succ j)))
                    * Real.log (∫ t, g (Function.update x (Fin.succ j) t) ∂(μ (Fin.succ j)))
                  ∂(Measure.pi μ)) := by
          intro j
          have Trev : ∀ (h : (∀ i, β i) → ℝ),
              Integrable (fun p : β 0 × (∀ k, β (Fin.succ k)) => h (Fin.cons p.1 p.2))
                ((μ 0).prod (Measure.pi (fun j => μ (Fin.succ j)))) →
              (∫ x, ∫ y, h (Fin.cons x y) ∂(Measure.pi (fun j => μ (Fin.succ j))) ∂(μ 0))
                = ∫ z, h z ∂(Measure.pi μ) := by
            intro h hint
            rw [integral_pi_eq_prod_cons μ h, integral_prod _ hint]
          set gMs : (∀ i, β i) → ℝ :=
            fun z => ∫ t, g (Function.update z (Fin.succ j) t) ∂(μ (Fin.succ j)) with hgMs
          obtain ⟨hgMsmeas, hgMslb, hgMsub⟩ := bddPos_marginal μ hmeas hcpos hlb hub (Fin.succ j)
          obtain ⟨hgMsCmeas, hgMsClb, hgMsCub⟩ := bddPos_cons hgMsmeas hcpos hgMslb hgMsub
          have hgMx : ∀ (x : β 0) (y : ∀ k, β (Fin.succ k)),
              (∫ t, g (Fin.cons x (Function.update y j t)) ∂(μ (Fin.succ j)))
                = gMs (Fin.cons x y) := by
            intro x y; rw [hgMs]; apply integral_congr_ae; filter_upwards with t; rw [Fin.cons_update]
          have hsplit : ∀ x : β 0,
              ((∫ y, g (Fin.cons x y) * Real.log (g (Fin.cons x y))
                    ∂(Measure.pi (fun j => μ (Fin.succ j))))
                - ∫ y, (∫ t, g (Fin.cons x (Function.update y j t)) ∂(μ (Fin.succ j)))
                    * Real.log (∫ t, g (Fin.cons x (Function.update y j t)) ∂(μ (Fin.succ j)))
                  ∂(Measure.pi (fun j => μ (Fin.succ j))))
              = (∫ y, g (Fin.cons x y) * Real.log (g (Fin.cons x y))
                    ∂(Measure.pi (fun j => μ (Fin.succ j))))
                - ∫ y, gMs (Fin.cons x y) * Real.log (gMs (Fin.cons x y))
                    ∂(Measure.pi (fun j => μ (Fin.succ j))) := by
            intro x; congr 1; apply integral_congr_ae; filter_upwards with y; rw [hgMx]
          simp_rw [hsplit]
          rw [integral_sub]
          · rw [Trev (fun z => g z * Real.log (g z))
                (bp_integrable_mul_log
                  (μ := (μ 0).prod (Measure.pi (fun j => μ (Fin.succ j))))
                  hFmeas hcpos hFlb hFub)]
            rw [Trev (fun z => gMs z * Real.log (gMs z))
                (bp_integrable_mul_log
                  (μ := (μ 0).prod (Measure.pi (fun j => μ (Fin.succ j))))
                  hgMsCmeas hcpos hgMsClb hgMsCub)]
          · exact (bp_integrable_mul_log
              (μ := (μ 0).prod (Measure.pi (fun j => μ (Fin.succ j))))
              hFmeas hcpos hFlb hFub).integral_prod_left
          · exact (bp_integrable_mul_log
              (μ := (μ 0).prod (Measure.pi (fun j => μ (Fin.succ j))))
              hgMsCmeas hcpos hgMsClb hgMsCub).integral_prod_left
        -- integrability of the fibre-j tail summand in x.
        have integrable_summand_succ : ∀ (j : Fin m),
            Integrable (fun x : β 0 =>
              (∫ y, g (Fin.cons x y) * Real.log (g (Fin.cons x y))
                    ∂(Measure.pi (fun j => μ (Fin.succ j))))
                - ∫ y, (∫ t, g (Fin.cons x (Function.update y j t)) ∂(μ (Fin.succ j)))
                      * Real.log (∫ t, g (Fin.cons x (Function.update y j t)) ∂(μ (Fin.succ j)))
                    ∂(Measure.pi (fun j => μ (Fin.succ j)))) (μ 0) := by
          intro j
          set gMs : (∀ i, β i) → ℝ :=
            fun z => ∫ t, g (Function.update z (Fin.succ j) t) ∂(μ (Fin.succ j)) with hgMs
          obtain ⟨hgMsmeas, hgMslb, hgMsub⟩ := bddPos_marginal μ hmeas hcpos hlb hub (Fin.succ j)
          obtain ⟨hgMsCmeas, hgMsClb, hgMsCub⟩ := bddPos_cons hgMsmeas hcpos hgMslb hgMsub
          have hgMx : ∀ (x : β 0) (y : ∀ k, β (Fin.succ k)),
              (∫ t, g (Fin.cons x (Function.update y j t)) ∂(μ (Fin.succ j)))
                = gMs (Fin.cons x y) := by
            intro x y; rw [hgMs]; apply integral_congr_ae; filter_upwards with t; rw [Fin.cons_update]
          have hcongr : (fun x : β 0 =>
              (∫ y, g (Fin.cons x y) * Real.log (g (Fin.cons x y))
                    ∂(Measure.pi (fun j => μ (Fin.succ j))))
                - ∫ y, (∫ t, g (Fin.cons x (Function.update y j t)) ∂(μ (Fin.succ j)))
                      * Real.log (∫ t, g (Fin.cons x (Function.update y j t)) ∂(μ (Fin.succ j)))
                    ∂(Measure.pi (fun j => μ (Fin.succ j))))
              = (fun x : β 0 =>
              (∫ y, g (Fin.cons x y) * Real.log (g (Fin.cons x y))
                    ∂(Measure.pi (fun j => μ (Fin.succ j))))
                - ∫ y, gMs (Fin.cons x y) * Real.log (gMs (Fin.cons x y))
                    ∂(Measure.pi (fun j => μ (Fin.succ j)))) := by
            funext x; congr 1; apply integral_congr_ae; filter_upwards with y; rw [hgMx]
          rw [hcongr]
          apply Integrable.sub
          · exact (bp_integrable_mul_log
              (μ := (μ 0).prod (Measure.pi (fun j => μ (Fin.succ j))))
              hFmeas hcpos hFlb hFub).integral_prod_left
          · exact (bp_integrable_mul_log
              (μ := (μ 0).prod (Measure.pi (fun j => μ (Fin.succ j))))
              hgMsCmeas hcpos hgMsClb hgMsCub).integral_prod_left
        -- pointwise: the fibre Ent ≤ ∑ summands (the induction hypothesis).
        have hpt : ∀ x : β 0,
            ((∫ y, F (x, y) * Real.log (F (x, y)) ∂Q)
              - (∫ y, F (x, y) ∂Q) * Real.log (∫ y, F (x, y) ∂Q))
            ≤ ∑ j : Fin m,
                ((∫ y, g (Fin.cons x y) * Real.log (g (Fin.cons x y))
                      ∂(Measure.pi (fun j => μ (Fin.succ j))))
                  - ∫ y, (∫ t, g (Fin.cons x (Function.update y j t)) ∂(μ (Fin.succ j)))
                        * Real.log (∫ t, g (Fin.cons x (Function.update y j t)) ∂(μ (Fin.succ j)))
                      ∂(Measure.pi (fun j => μ (Fin.succ j)))) := by
          intro x
          exact ih (fun j => μ (Fin.succ j)) (g := fun y => g (Fin.cons x y)) (c := c) (C := C)
            (hmeas.comp measurable_cons |>.comp (measurable_const.prodMk measurable_id))
            hcpos (fun y => hlb (Fin.cons x y)) (fun y => hub (Fin.cons x y))
        calc (∫ x, ((∫ y, F (x, y) * Real.log (F (x, y)) ∂Q)
                - (∫ y, F (x, y) ∂Q) * Real.log (∫ y, F (x, y) ∂Q)) ∂ρ)
            ≤ ∫ x, (∑ j : Fin m,
                ((∫ y, g (Fin.cons x y) * Real.log (g (Fin.cons x y))
                      ∂(Measure.pi (fun j => μ (Fin.succ j))))
                  - ∫ y, (∫ t, g (Fin.cons x (Function.update y j t)) ∂(μ (Fin.succ j)))
                        * Real.log (∫ t, g (Fin.cons x (Function.update y j t)) ∂(μ (Fin.succ j)))
                      ∂(Measure.pi (fun j => μ (Fin.succ j))))) ∂ρ := by
              apply integral_mono _ _ hpt
              · apply Integrable.sub
                · exact (bp_integrable_mul_log (μ := ρ.prod Q) hFmeas hcpos hFlb hFub).integral_prod_left
                · obtain ⟨hsmeas, hslb, hsub⟩ := bddPos_integral_snd Q hFmeas hcpos hFlb hFub
                  exact bp_integrable_mul_log (μ := ρ) hsmeas hcpos hslb hsub
              · exact integrable_finset_sum _ (fun j _ => integrable_summand_succ j)
          _ = ∑ j : Fin m, ∫ x,
                ((∫ y, g (Fin.cons x y) * Real.log (g (Fin.cons x y))
                      ∂(Measure.pi (fun j => μ (Fin.succ j))))
                  - ∫ y, (∫ t, g (Fin.cons x (Function.update y j t)) ∂(μ (Fin.succ j)))
                        * Real.log (∫ t, g (Fin.cons x (Function.update y j t)) ∂(μ (Fin.succ j)))
                      ∂(Measure.pi (fun j => μ (Fin.succ j)))) ∂ρ := by
              rw [integral_finset_sum]; intro j _; exact integrable_summand_succ j
          _ = ∑ j : Fin m,
                ((∫ x, g x * Real.log (g x) ∂(Measure.pi μ))
                  - ∫ x, (∫ t, g (Function.update x (Fin.succ j) t) ∂(μ (Fin.succ j)))
                      * Real.log (∫ t, g (Function.update x (Fin.succ j) t) ∂(μ (Fin.succ j)))
                    ∂(Measure.pi μ)) := by
              apply Finset.sum_congr rfl; intro j _; exact summand_succ_eq j
      rw [hCol, Fin.sum_univ_succ]
      gcongr
  ----------------------------------------------------------------------------
  -- Apply `key`.
  ----------------------------------------------------------------------------
  exact key n μ (g := g) (c := c) (C := C) hmeas hcpos hlb hub

#print axioms solution
