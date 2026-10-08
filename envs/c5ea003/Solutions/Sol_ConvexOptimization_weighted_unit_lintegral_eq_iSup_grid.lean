-- Prove2me | solution 1 for ConvexOptimization.weighted_unit_lintegral_eq_iSup_grid
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-16T19:26:02.012697+00:00
-- url     : https://prove2.me/submissions/78814045-3e2e-401a-9ba2-e0ee4f9040b3

import Theorems.Thm_ConvexOptimization_brunn_minkowski_real_line_weighted

open scoped RealInnerProductSpace ENNReal
open MeasureTheory
open Filter Topology

set_option maxHeartbeats 1000000

namespace WULAux

open Filter Topology

/-- The number of grid levels of `{δ, 2δ, …, Nδ}` (with `δ = 1/(N+1)`) that lie below `a`. -/
noncomputable def Sc (N : ℕ) (a : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i : Fin N, if (((i.val + 1 : ℕ) : ℝ≥0∞) / ((N + 1 : ℕ) : ℝ≥0∞)) ≤ a then 1 else 0

theorem Sc_eq (N : ℕ) (a : ℝ≥0∞) (ha : a ≤ 1) :
    Sc N a = ((min N ⌊a.toReal * ((N : ℝ) + 1)⌋₊ : ℕ) : ℝ≥0∞) := by
  classical
  have hatop : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha
  have hanm : (0 : ℝ) ≤ a.toReal * ((N : ℝ) + 1) := by positivity
  have hiff : ∀ i : Fin N,
      ((((i.val + 1 : ℕ) : ℝ≥0∞) / ((N + 1 : ℕ) : ℝ≥0∞)) ≤ a)
        ↔ (i.val < ⌊a.toReal * ((N : ℝ) + 1)⌋₊) := by
    intro i
    rw [ENNReal.div_le_iff_le_mul (Or.inl (by simp)) (Or.inl (by simp))]
    rw [← ENNReal.toReal_le_toReal (by simp) (ENNReal.mul_ne_top hatop (by simp))]
    rw [ENNReal.toReal_mul]
    simp only [ENNReal.toReal_natCast]
    constructor
    · intro h
      have h2 : ((i.val + 1 : ℕ) : ℝ) ≤ a.toReal * ((N : ℝ) + 1) := by push_cast at h ⊢; linarith
      have h3 := (Nat.le_floor_iff hanm).mpr h2
      omega
    · intro h
      have h3 : (i.val + 1 : ℕ) ≤ ⌊a.toReal * ((N : ℝ) + 1)⌋₊ := h
      have h2 := (Nat.le_floor_iff hanm).mp h3
      push_cast at h2 ⊢
      linarith
  have h1 : Sc N a = ∑ i : Fin N,
      (if i.val < ⌊a.toReal * ((N : ℝ) + 1)⌋₊ then (1 : ℝ≥0∞) else 0) :=
    Finset.sum_congr rfl fun i _ => if_congr (hiff i) rfl rfl
  rw [h1, Fin.sum_univ_eq_sum_range
    (fun k => if k < ⌊a.toReal * ((N : ℝ) + 1)⌋₊ then (1 : ℝ≥0∞) else 0) N]
  rw [Finset.sum_boole]
  congr 1
  have hset : (Finset.range N).filter (fun k => k < ⌊a.toReal * ((N : ℝ) + 1)⌋₊)
      = Finset.range (min N ⌊a.toReal * ((N : ℝ) + 1)⌋₊) := by
    ext k
    simp [Finset.mem_range]
  rw [hset, Finset.card_range]

theorem Sc_le (N : ℕ) (a : ℝ≥0∞) (ha : a ≤ 1) :
    ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ * Sc N a ≤ a := by
  classical
  have hatop : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha
  have hanm : (0 : ℝ) ≤ a.toReal * ((N : ℝ) + 1) := by positivity
  set m : ℕ := ⌊a.toReal * ((N : ℝ) + 1)⌋₊ with hm
  rw [Sc_eq N a ha, ← ENNReal.div_eq_inv_mul]
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by simp)) (Or.inl (by simp))]
  rw [← ENNReal.toReal_le_toReal (by simp) (ENNReal.mul_ne_top hatop (by simp))]
  rw [ENNReal.toReal_mul]
  simp only [ENNReal.toReal_natCast]
  have hmin : ((min N m : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.cast_le.mpr (min_le_right N m)
  have hfl : (m : ℝ) ≤ a.toReal * ((N : ℝ) + 1) := by
    rw [hm]; exact Nat.floor_le hanm
  have hcast : (((N : ℕ) + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  linarith

theorem le_Sc (N : ℕ) (a : ℝ≥0∞) (ha : a ≤ 1) :
    a ≤ ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ * Sc N a + ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  have hatop : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha
  have hanm : (0 : ℝ) ≤ a.toReal * ((N : ℝ) + 1) := by positivity
  set m : ℕ := ⌊a.toReal * ((N : ℝ) + 1)⌋₊ with hm
  have hcomb : ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ * Sc N a + ((N + 1 : ℕ) : ℝ≥0∞)⁻¹
      = (((min N m + 1 : ℕ) : ℝ≥0∞)) / ((N + 1 : ℕ) : ℝ≥0∞) := by
    rw [Sc_eq N a ha, ← hm, ENNReal.div_eq_inv_mul]
    push_cast
    ring
  rw [hcomb, ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))]
  rw [← ENNReal.toReal_le_toReal (ENNReal.mul_ne_top hatop (by simp)) (by simp)]
  rw [ENNReal.toReal_mul]
  simp only [ENNReal.toReal_natCast]
  have hcast : (((N : ℕ) + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have ha1 : a.toReal ≤ 1 := by
    have := ENNReal.toReal_le_toReal hatop ENNReal.one_ne_top |>.mpr ha
    simpa using this
  rcases le_or_gt m N with hc | hc
  · have hmin : min N m = m := min_eq_right hc
    rw [hmin]
    have hlt := Nat.lt_floor_add_one (a.toReal * ((N : ℝ) + 1))
    rw [← hm] at hlt
    push_cast
    linarith
  · have hmin : min N m = N := min_eq_left hc.le
    rw [hmin]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) N, ENNReal.toReal_nonneg (a := a)]

/-! ### The discretised integrand -/

/-- The uniform lower layer-cake approximation of `(1-l)f + l g`. -/
noncomputable def Ph (l : ℝ) (f g : ℝ → ℝ≥0∞) (N : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ *
    ∑ i : Fin N,
      (ENNReal.ofReal (1 - l) *
          (if (((i.val + 1 : ℕ) : ℝ≥0∞) / ((N + 1 : ℕ) : ℝ≥0∞)) ≤ f x then 1 else 0)
        + ENNReal.ofReal l *
          (if (((i.val + 1 : ℕ) : ℝ≥0∞) / ((N + 1 : ℕ) : ℝ≥0∞)) ≤ g x then 1 else 0))

theorem Ph_eq (l : ℝ) (f g : ℝ → ℝ≥0∞) (N : ℕ) (x : ℝ) :
    Ph l f g N x
      = ENNReal.ofReal (1 - l) * (((N + 1 : ℕ) : ℝ≥0∞)⁻¹ * Sc N (f x))
        + ENNReal.ofReal l * (((N + 1 : ℕ) : ℝ≥0∞)⁻¹ * Sc N (g x)) := by
  classical
  rw [Ph, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Sc, Sc]
  ring

theorem Ph_meas (l : ℝ) (f g : ℝ → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) (N : ℕ) :
    Measurable (Ph l f g N) := by
  classical
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.add (Measurable.const_mul ?_ _) (Measurable.const_mul ?_ _)
  · exact Measurable.ite (measurableSet_le measurable_const hf) measurable_const measurable_const
  · exact Measurable.ite (measurableSet_le measurable_const hg) measurable_const measurable_const

theorem lintegral_ite_le (c : ℝ≥0∞) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, (if c ≤ f x then (1 : ℝ≥0∞) else 0) = volume {x : ℝ | c ≤ f x} := by
  have hs : MeasurableSet {x : ℝ | c ≤ f x} := measurableSet_le measurable_const hf
  have hrw : (fun x => if c ≤ f x then (1 : ℝ≥0∞) else 0)
      = {x : ℝ | c ≤ f x}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : c ≤ f x
    · rw [if_pos hx, Set.indicator_of_mem (show x ∈ {x : ℝ | c ≤ f x} from hx)]
    · rw [if_neg hx, Set.indicator_of_notMem (show x ∉ {x : ℝ | c ≤ f x} from hx)]
  rw [hrw, lintegral_indicator_const hs, one_mul]

theorem lintegral_Ph (l : ℝ) (f g : ℝ → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) (N : ℕ) :
    ∫⁻ x, Ph l f g N x
      = ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ *
        ∑ i : Fin N,
          (ENNReal.ofReal (1 - l) *
              volume {x : ℝ | (((i.val + 1 : ℕ) : ℝ≥0∞) / ((N + 1 : ℕ) : ℝ≥0∞)) ≤ f x}
            + ENNReal.ofReal l *
              volume {y : ℝ | (((i.val + 1 : ℕ) : ℝ≥0∞) / ((N + 1 : ℕ) : ℝ≥0∞)) ≤ g y}) := by
  simp only [Ph]
  rw [lintegral_const_mul' _ _ (by simp : ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ ≠ ⊤)]
  congr 1
  rw [lintegral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_add_left]
    · rw [lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (1 - l) ≠ ⊤),
        lintegral_const_mul' _ _ (by simp : ENNReal.ofReal l ≠ ⊤)]
      congr 1
      · exact congrArg _ (lintegral_ite_le _ f hf)
      · exact congrArg _ (lintegral_ite_le _ g hg)
    · exact Measurable.const_mul
        (Measurable.ite (measurableSet_le measurable_const hf) measurable_const measurable_const) _
  · intro i _
    refine Measurable.add (Measurable.const_mul ?_ _) (Measurable.const_mul ?_ _)
    · exact Measurable.ite (measurableSet_le measurable_const hf) measurable_const measurable_const
    · exact Measurable.ite (measurableSet_le measurable_const hg) measurable_const measurable_const

end WULAux

open WULAux in
/-- **Uniform-grid layer-cake representation** of the weighted lower integral. -/
theorem solution
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1) :
    ENNReal.ofReal (1 - l) * (∫⁻ x, f x) +
        ENNReal.ofReal l * (∫⁻ x, g x) =
      ⨆ N : {N : ℕ // 0 < N},
        (((N.1 + 1 : ℕ) : ℝ≥0∞)⁻¹ *
          ∑ i : Fin N.1,
            (ENNReal.ofReal (1 - l) * volume
                {x : ℝ | (((i.val + 1 : ℕ) : ℝ≥0∞) / (N.1 + 1 : ℕ)) ≤ f x} +
              ENNReal.ofReal l * volume
                {y : ℝ | (((i.val + 1 : ℕ) : ℝ≥0∞) / (N.1 + 1 : ℕ)) ≤ g y})) := by
  classical
  set T : ℕ → ℝ≥0∞ := fun N =>
    ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ *
      ∑ i : Fin N,
        (ENNReal.ofReal (1 - l) * volume
            {x : ℝ | (((i.val + 1 : ℕ) : ℝ≥0∞) / ((N + 1 : ℕ) : ℝ≥0∞)) ≤ f x} +
          ENNReal.ofReal l * volume
            {y : ℝ | (((i.val + 1 : ℕ) : ℝ≥0∞) / ((N + 1 : ℕ) : ℝ≥0∞)) ≤ g y}) with hT
  have hTint : ∀ N, T N = ∫⁻ x, Ph l f g N x := fun N => (lintegral_Ph l f g hf hg N).symm
  set Φ : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (1 - l) * f x + ENNReal.ofReal l * g x with hΦ
  have hab : ENNReal.ofReal (1 - l) + ENNReal.ofReal l = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
    norm_num
  have hΦle : ∀ x, Φ x ≤ 1 := by
    intro x
    have h1 : ENNReal.ofReal (1 - l) * f x ≤ ENNReal.ofReal (1 - l) * 1 :=
      mul_le_mul_left' (hf1 x) _
    have h2 : ENNReal.ofReal l * g x ≤ ENNReal.ofReal l * 1 := mul_le_mul_left' (hg1 x) _
    calc Φ x ≤ ENNReal.ofReal (1 - l) * 1 + ENNReal.ofReal l * 1 := add_le_add h1 h2
      _ = 1 := by rw [mul_one, mul_one, hab]
  have hΦint : ∫⁻ x, Φ x
      = ENNReal.ofReal (1 - l) * (∫⁻ x, f x) + ENNReal.ofReal l * (∫⁻ x, g x) := by
    rw [hΦ]
    rw [lintegral_add_left (hf.const_mul _)]
    rw [lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (1 - l) ≠ ⊤),
      lintegral_const_mul' _ _ (by simp : ENNReal.ofReal l ≠ ⊤)]
  have hΦmeas : Measurable Φ := (hf.const_mul _).add (hg.const_mul _)
  -- pointwise sandwich
  have hle : ∀ N x, Ph l f g N x ≤ Φ x := by
    intro N x
    rw [Ph_eq, hΦ]
    exact add_le_add (mul_le_mul_left' (Sc_le N (f x) (hf1 x)) _)
      (mul_le_mul_left' (Sc_le N (g x) (hg1 x)) _)
  have hge : ∀ N x, Φ x ≤ Ph l f g N x + ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    intro N x
    have h1 := le_Sc N (f x) (hf1 x)
    have h2 := le_Sc N (g x) (hg1 x)
    calc Φ x ≤ ENNReal.ofReal (1 - l) *
            (((N + 1 : ℕ) : ℝ≥0∞)⁻¹ * Sc N (f x) + ((N + 1 : ℕ) : ℝ≥0∞)⁻¹)
          + ENNReal.ofReal l *
            (((N + 1 : ℕ) : ℝ≥0∞)⁻¹ * Sc N (g x) + ((N + 1 : ℕ) : ℝ≥0∞)⁻¹) := by
          rw [hΦ]
          exact add_le_add (mul_le_mul_left' h1 _) (mul_le_mul_left' h2 _)
      _ = Ph l f g N x + (ENNReal.ofReal (1 - l) + ENNReal.ofReal l)
            * ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
          rw [Ph_eq]; ring
      _ = Ph l f g N x + ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ := by rw [hab, one_mul]
  -- the supremum over the subtype is the supremum over shifted naturals
  have hsup : (⨆ N : {N : ℕ // 0 < N}, T N.1) = ⨆ k : ℕ, T (k + 1) := by
    apply le_antisymm
    · refine iSup_le fun N => ?_
      have hN : N.1 - 1 + 1 = N.1 := Nat.succ_pred_eq_of_pos N.2
      calc T N.1 = T (N.1 - 1 + 1) := by rw [hN]
        _ ≤ ⨆ k : ℕ, T (k + 1) := le_iSup (fun k : ℕ => T (k + 1)) (N.1 - 1)
    · exact iSup_le fun k => le_iSup (fun N : {N : ℕ // 0 < N} => T N.1) ⟨k + 1, by omega⟩
  rw [← hΦint, hsup]
  apply le_antisymm
  · -- Fatou
    have htend : ∀ x, Tendsto (fun k : ℕ => Ph l f g (k + 1) x) atTop (𝓝 (Φ x)) := by
      intro x
      rw [ENNReal.tendsto_nhds (ne_top_of_le_ne_top ENNReal.one_ne_top (hΦle x))]
      intro ε hε
      have h0 : ∀ᶠ n : ℕ in atTop, ((n : ℕ) : ℝ≥0∞)⁻¹ < ε :=
        ENNReal.tendsto_inv_nat_nhds_zero.eventually_lt_const hε
      have h1 : ∀ᶠ k : ℕ in atTop, (((k + 1 + 1 : ℕ)) : ℝ≥0∞)⁻¹ < ε :=
        (Filter.tendsto_add_atTop_nat 2).eventually h0
      filter_upwards [h1] with k hk
      refine ⟨?_, ?_⟩
      · refine tsub_le_iff_right.mpr ?_
        exact le_trans (hge (k + 1) x) (add_le_add le_rfl hk.le)
      · exact le_trans (hle (k + 1) x) le_self_add
    have hlim : ∀ x, liminf (fun k : ℕ => Ph l f g (k + 1) x) atTop = Φ x :=
      fun x => (htend x).liminf_eq
    calc ∫⁻ x, Φ x = ∫⁻ x, liminf (fun k : ℕ => Ph l f g (k + 1) x) atTop := by
          simp_rw [hlim]
      _ ≤ liminf (fun k : ℕ => ∫⁻ x, Ph l f g (k + 1) x) atTop :=
          lintegral_liminf_le (fun k => Ph_meas l f g hf hg (k + 1))
      _ ≤ ⨆ k : ℕ, ∫⁻ x, Ph l f g (k + 1) x := le_trans liminf_le_limsup limsup_le_iSup
      _ = ⨆ k : ℕ, T (k + 1) := by simp_rw [hTint]
  · refine iSup_le fun k => ?_
    rw [hTint]
    exact lintegral_mono fun x => hle (k + 1) x
