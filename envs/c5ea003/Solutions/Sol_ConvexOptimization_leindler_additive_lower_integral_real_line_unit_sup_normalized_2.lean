-- Prove2me | solution 2 for ConvexOptimization.leindler_additive_lower_integral_real_line_unit_sup_normalized
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-15T07:58:01.825888+00:00
-- url     : https://prove2.me/submissions/bb6168da-8aea-4da0-a7f7-1d1e997923c6

import Theorems.Thm_ConvexOptimization_brunn_minkowski_real_line_weighted

open scoped RealInnerProductSpace ENNReal Pointwise
open MeasureTheory Set

private theorem envelope_lintegral_lt_top
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g : ℝ → ℝ≥0∞)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1) :
    (∫⁻ z, sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
      (1 - l) • x + l • y = z ∧
        q = f x ^ (1 - l) * g y ^ l}) < ∞ := by
  let S : Set ℝ := (1 - l) • tsupport f + l • tsupport g
  have hSc : IsCompact S := (hfc.smul (1 - l)).add (hgc.smul l)
  calc
    (∫⁻ z, sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
      (1 - l) • x + l • y = z ∧
        q = f x ^ (1 - l) * g y ^ l}) ≤
        ∫⁻ z, S.indicator (fun _ ↦ (1 : ℝ≥0∞)) z := by
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem hz]
        apply sSup_le
        intro q hq
        rcases hq with ⟨x, y, hxy, rfl⟩
        exact mul_le_one₀
          (ENNReal.rpow_le_one (hf1 x) (sub_nonneg.mpr hl1.le))
          zero_le
          (ENNReal.rpow_le_one (hg1 y) hl0.le)
      · rw [Set.indicator_of_notMem hz]
        apply sSup_le
        intro q hq
        rcases hq with ⟨x, y, hxy, rfl⟩
        by_cases hx : x ∈ tsupport f
        · have hy : y ∉ tsupport g := by
            intro hy
            apply hz
            exact ⟨(1 - l) • x, ⟨x, hx, rfl⟩,
              l • y, ⟨y, hy, rfl⟩, hxy⟩
          rw [image_eq_zero_of_notMem_tsupport hy]
          simp [ENNReal.zero_rpow_of_pos hl0]
        · rw [image_eq_zero_of_notMem_tsupport hx]
          simp [ENNReal.zero_rpow_of_pos (sub_pos.mpr hl1)]
    _ ≤ volume S := lintegral_indicator_one_le S
    _ < ∞ := hSc.measure_lt_top

private theorem compact_chain_sum_le
    (N : ℕ) (hN : 0 < N)
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g : ℝ → ℝ≥0∞)
    (K L : Fin N → Set ℝ)
    (hKc : ∀ i, IsCompact (K i)) (hLc : ∀ i, IsCompact (L i))
    (hKn : ∀ i, (K i).Nonempty) (hLn : ∀ i, (L i).Nonempty)
    (hKanti : ∀ i j, i ≤ j → K j ⊆ K i)
    (hLanti : ∀ i j, i ≤ j → L j ⊆ L i)
    (hKlev : ∀ i x, x ∈ K i →
      ((i.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ) ≤ f x)
    (hLlev : ∀ i y, y ∈ L i →
      ((i.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ) ≤ g y) :
    ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ *
        ∑ i : Fin N, volume ((1 - l) • K i + l • L i) ≤
      ∫⁻ z, sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
        (1 - l) • x + l • y = z ∧
          q = f x ^ (1 - l) * g y ^ l} := by
  classical
  let δ : ℝ≥0∞ := ((N + 1 : ℕ) : ℝ≥0∞)⁻¹
  let C : Fin N → Set ℝ := fun i ↦ (1 - l) • K i + l • L i
  let H : ℝ → ℝ≥0∞ := fun z ↦ ∑ i : Fin N, (C i).indicator (fun _ ↦ δ) z
  have hCc : ∀ i, IsCompact (C i) := by
    intro i
    exact (hKc i).smul (1 - l) |>.add ((hLc i).smul l)
  have hCm : ∀ i, MeasurableSet (C i) := fun i ↦ (hCc i).measurableSet
  have hCanti : ∀ i j, i ≤ j → C j ⊆ C i := by
    intro i j hij
    exact add_subset_add (smul_set_mono (hKanti i j hij))
      (smul_set_mono (hLanti i j hij))
  have hHmeas : Measurable H := by
    dsimp only [H]
    exact Finset.measurable_sum _ fun i _ ↦ measurable_const.indicator (hCm i)
  have hHint : (∫⁻ z, H z) = δ * ∑ i : Fin N, volume (C i) := by
    rw [lintegral_finsetSum]
    · simp_rw [lintegral_indicator_const (hCm _) δ]
      rw [Finset.mul_sum]
    · intro i hi
      exact measurable_const.indicator (hCm i)
  have hHle : H ≤ fun z ↦ sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
      (1 - l) • x + l • y = z ∧
        q = f x ^ (1 - l) * g y ^ l} := by
    intro z
    let I : Finset (Fin N) := Finset.univ.filter fun i ↦ z ∈ C i
    by_cases hI : I.Nonempty
    · let m : Fin N := I.max' hI
      have hmI : m ∈ I := Finset.max'_mem I hI
      have hIeq : I = Finset.Iic m := by
        ext i
        constructor
        · intro hi
          exact Finset.mem_Iic.mpr (Finset.le_max' I i hi)
        · intro hi
          have him : i ≤ m := Finset.mem_Iic.mp hi
          have hmC : z ∈ C m := (Finset.mem_filter.mp hmI).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCanti i m him hmC⟩
      have hHeq : H z = ((m.val + 1 : ℕ) : ℝ≥0∞) * δ := by
        calc
          H z = ∑ i : Fin N, if z ∈ C i then δ else 0 := by
            simp only [H, Set.indicator]
          _ = δ * ∑ i : Fin N, if z ∈ C i then 1 else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            split_ifs <;> simp
          _ = δ * (I.card : ℝ≥0∞) := by
            rw [Finset.sum_boole]
          _ = (I.card : ℝ≥0∞) * δ := mul_comm _ _
          _ = ((m.val + 1 : ℕ) : ℝ≥0∞) * δ := by rw [hIeq, Fin.card_Iic]
      rw [hHeq]
      have hmC : z ∈ C m := (Finset.mem_filter.mp hmI).2
      rcases hmC with ⟨u, hu, v, hv, huv⟩
      rcases hu with ⟨x, hx, rfl⟩
      rcases hv with ⟨y, hy, rfl⟩
      have htpos : 0 < (((m.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ)) := by
        apply ENNReal.div_pos
        · simp
        · simp
      have httop : (((m.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ)) ≠ ∞ := by
        finiteness
      have hprod :
          (((m.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ)) ≤
            f x ^ (1 - l) * g y ^ l := by
        calc
          (((m.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ)) =
              (((m.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ)) ^ (1 - l) *
                (((m.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ)) ^ l := by
            rw [← ENNReal.rpow_add (1 - l) l htpos.ne' httop]
            norm_num
          _ ≤ f x ^ (1 - l) * g y ^ l :=
            mul_le_mul'
              (ENNReal.rpow_le_rpow (hKlev m x hx) (sub_nonneg.mpr hl1.le))
              (ENNReal.rpow_le_rpow (hLlev m y hy) hl0.le)
      have henvelope : f x ^ (1 - l) * g y ^ l ≤
          sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
            (1 - l) • x + l • y = z ∧
              q = f x ^ (1 - l) * g y ^ l} := by
        apply le_sSup
        exact ⟨x, y, huv, rfl⟩
      simpa [δ, ENNReal.div_eq_inv_mul, mul_comm] using hprod.trans henvelope
    · have hIz : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
      have hHzero : H z = 0 := by
        have hznot : ∀ i, z ∉ C i := by
          intro i hi
          apply hI
          exact ⟨i, by simp [I, hi]⟩
        simp [H, Set.indicator, hznot]
      rw [hHzero]
      exact bot_le
  change δ * ∑ i : Fin N, volume (C i) ≤ _
  rw [← hHint]
  exact lintegral_mono hHle

private theorem grid_tail_sum_le
    (N : ℕ) (hN : 0 < N)
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (hfsup : sSup (Set.range f) = 1)
    (hgsup : sSup (Set.range g) = 1) :
    ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ *
        ∑ i : Fin N,
          (ENNReal.ofReal (1 - l) * volume
              {x : ℝ | (((i.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ)) ≤ f x} +
            ENNReal.ofReal l * volume
              {y : ℝ | (((i.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ)) ≤ g y}) ≤
      ∫⁻ z, sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
        (1 - l) • x + l • y = z ∧
          q = f x ^ (1 - l) * g y ^ l} := by
  classical
  let δ : ℝ≥0∞ := ((N + 1 : ℕ) : ℝ≥0∞)⁻¹
  let t : Fin N → ℝ≥0∞ := fun i ↦
    ((i.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ)
  let A : Fin N → Set ℝ := fun i ↦ {x | t i ≤ f x}
  let B : Fin N → Set ℝ := fun i ↦ {y | t i ≤ g y}
  let a : ℝ≥0∞ := ENNReal.ofReal (1 - l)
  let b : ℝ≥0∞ := ENNReal.ofReal l
  let R : ℝ≥0∞ := ∫⁻ z, sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
    (1 - l) • x + l • y = z ∧
      q = f x ^ (1 - l) * g y ^ l}
  have hatop : a ≠ ∞ := ENNReal.ofReal_ne_top
  have hbtop : b ≠ ∞ := ENNReal.ofReal_ne_top
  have hab : a + b = 1 := by
    have hnn : Real.toNNReal (1 - l) + Real.toNNReal l = 1 := by
      apply NNReal.eq
      simp [(sub_pos.mpr hl1).le, hl0.le]
    simpa [a, b, ENNReal.ofReal] using congrArg (fun r : NNReal ↦ (r : ENNReal)) hnn
  have htmono : Monotone t := by
    intro i j hij
    dsimp only [t]
    simp only [ENNReal.div_eq_inv_mul]
    apply mul_le_mul_left'
    exact_mod_cast Nat.succ_le_succ hij
  have htlt : ∀ i, t i < 1 := by
    intro i
    dsimp only [t]
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp))]
    simp only [one_mul]
    exact_mod_cast Nat.succ_lt_succ i.isLt
  have htpos : ∀ i, 0 < t i := by
    intro i
    dsimp only [t]
    apply ENNReal.div_pos
    · simp
    · simp
  have hAm : ∀ i, MeasurableSet (A i) := by
    intro i
    exact measurableSet_le measurable_const hf
  have hBm : ∀ i, MeasurableSet (B i) := by
    intro i
    exact measurableSet_le measurable_const hg
  have hAanti : ∀ i j, i ≤ j → A j ⊆ A i := by
    intro i j hij x hx
    exact (htmono hij).trans hx
  have hBanti : ∀ i j, i ≤ j → B j ⊆ B i := by
    intro i j hij x hx
    exact (htmono hij).trans hx
  have hAn : ∀ i, (A i).Nonempty := by
    intro i
    have hi : t i < sSup (Set.range f) := by simpa [hfsup] using htlt i
    rcases lt_sSup_iff.mp hi with ⟨q, ⟨x, rfl⟩, hx⟩
    exact ⟨x, hx.le⟩
  have hBn : ∀ i, (B i).Nonempty := by
    intro i
    have hi : t i < sSup (Set.range g) := by simpa [hgsup] using htlt i
    rcases lt_sSup_iff.mp hi with ⟨q, ⟨x, rfl⟩, hx⟩
    exact ⟨x, hx.le⟩
  have hAfin : ∀ i, volume (A i) ≠ ∞ := by
    intro i
    apply ne_top_of_le_ne_top (hfc.measure_lt_top (μ := volume)).ne
    apply measure_mono
    intro x hx
    by_contra hxs
    change t i ≤ f x at hx
    have := hx
    rw [image_eq_zero_of_notMem_tsupport hxs] at this
    exact (not_le_of_gt (htpos i)) this
  have hBfin : ∀ i, volume (B i) ≠ ∞ := by
    intro i
    apply ne_top_of_le_ne_top (hgc.measure_lt_top (μ := volume)).ne
    apply measure_mono
    intro x hx
    by_contra hxs
    change t i ≤ g x at hx
    have := hx
    rw [image_eq_zero_of_notMem_tsupport hxs] at this
    exact (not_le_of_gt (htpos i)) this
  have hRtop : R < ∞ := envelope_lintegral_lt_top l hl0 hl1 f g hfc hgc hf1 hg1
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hR
  have hεne : (ε : ℝ≥0∞) ≠ 0 := by exact_mod_cast hε.ne'
  have hexK : ∀ i, ∃ K₀ : Set ℝ, K₀ ⊆ A i ∧ IsCompact K₀ ∧
      volume (A i) < volume K₀ + (ε : ℝ≥0∞) := by
    intro i
    rcases (hAm i).exists_isCompact_lt_add (hAfin i) hεne with
      ⟨K₀, hK₀A, hK₀c, hK₀ε⟩
    exact ⟨K₀, hK₀A, hK₀c, hK₀ε⟩
  have hexL : ∀ i, ∃ L₀ : Set ℝ, L₀ ⊆ B i ∧ IsCompact L₀ ∧
      volume (B i) < volume L₀ + (ε : ℝ≥0∞) := by
    intro i
    rcases (hBm i).exists_isCompact_lt_add (hBfin i) hεne with
      ⟨L₀, hL₀B, hL₀c, hL₀ε⟩
    exact ⟨L₀, hL₀B, hL₀c, hL₀ε⟩
  choose K₀ hK₀A hK₀c hK₀ε using hexK
  choose L₀ hL₀B hL₀c hL₀ε using hexL
  choose x₀ hx₀ using hAn
  choose y₀ hy₀ using hBn
  let K₁ : Fin N → Set ℝ := fun i ↦ K₀ i ∪ {x₀ i}
  let L₁ : Fin N → Set ℝ := fun i ↦ L₀ i ∪ {y₀ i}
  have hK₁A : ∀ i, K₁ i ⊆ A i := fun i ↦ union_subset (hK₀A i)
    (singleton_subset_iff.mpr (hx₀ i))
  have hL₁B : ∀ i, L₁ i ⊆ B i := fun i ↦ union_subset (hL₀B i)
    (singleton_subset_iff.mpr (hy₀ i))
  have hK₁c : ∀ i, IsCompact (K₁ i) := fun i ↦ (hK₀c i).union isCompact_singleton
  have hL₁c : ∀ i, IsCompact (L₁ i) := fun i ↦ (hL₀c i).union isCompact_singleton
  have hK₁n : ∀ i, (K₁ i).Nonempty := fun i ↦
    ⟨x₀ i, Or.inr (mem_singleton (x₀ i))⟩
  have hL₁n : ∀ i, (L₁ i).Nonempty := fun i ↦
    ⟨y₀ i, Or.inr (mem_singleton (y₀ i))⟩
  let K : Fin N → Set ℝ := fun i ↦ ⋃ j ∈ Finset.Ici i, K₁ j
  let L : Fin N → Set ℝ := fun i ↦ ⋃ j ∈ Finset.Ici i, L₁ j
  have hKc : ∀ i, IsCompact (K i) := by
    intro i
    exact Finset.isCompact_biUnion (Finset.Ici i) fun j hj ↦ hK₁c j
  have hLc : ∀ i, IsCompact (L i) := by
    intro i
    exact Finset.isCompact_biUnion (Finset.Ici i) fun j hj ↦ hL₁c j
  have hKn : ∀ i, (K i).Nonempty := by
    intro i
    rcases hK₁n i with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simp only [K, mem_iUnion]
    exact ⟨i, Finset.mem_Ici.mpr le_rfl, hx⟩
  have hLn : ∀ i, (L i).Nonempty := by
    intro i
    rcases hL₁n i with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simp only [L, mem_iUnion]
    exact ⟨i, Finset.mem_Ici.mpr le_rfl, hx⟩
  have hKA : ∀ i, K i ⊆ A i := by
    intro i x hx
    simp only [K, mem_iUnion] at hx
    rcases hx with ⟨j, hj⟩
    rcases hj with ⟨hij, hxj⟩
    exact hAanti i j (Finset.mem_Ici.mp hij) (hK₁A j hxj)
  have hLB : ∀ i, L i ⊆ B i := by
    intro i x hx
    simp only [L, mem_iUnion] at hx
    rcases hx with ⟨j, hj⟩
    rcases hj with ⟨hij, hxj⟩
    exact hBanti i j (Finset.mem_Ici.mp hij) (hL₁B j hxj)
  have hKanti : ∀ i j, i ≤ j → K j ⊆ K i := by
    intro i j hij x hx
    simp only [K, mem_iUnion] at hx ⊢
    rcases hx with ⟨k, hk, hxk⟩
    exact ⟨k, Finset.mem_Ici.mpr (hij.trans (Finset.mem_Ici.mp hk)), hxk⟩
  have hLanti : ∀ i j, i ≤ j → L j ⊆ L i := by
    intro i j hij x hx
    simp only [L, mem_iUnion] at hx ⊢
    rcases hx with ⟨k, hk, hxk⟩
    exact ⟨k, Finset.mem_Ici.mpr (hij.trans (Finset.mem_Ici.mp hk)), hxk⟩
  have hcompact : δ * ∑ i : Fin N,
      (a * volume (K i) + b * volume (L i)) ≤ R := by
    calc
      δ * ∑ i : Fin N, (a * volume (K i) + b * volume (L i)) ≤
          δ * ∑ i : Fin N, volume ((1 - l) • K i + l • L i) := by
        gcongr with i
        exact ConvexOptimization.brunn_minkowski_real_line_weighted
          l hl0 hl1 (K i) (L i) (hKc i).measurableSet (hLc i).measurableSet
            (hKn i) (hLn i)
      _ ≤ R := by
        exact compact_chain_sum_le N hN l hl0 hl1 f g K L hKc hLc hKn hLn
          hKanti hLanti (fun i x hx ↦ hKA i hx) (fun i y hy ↦ hLB i hy)
  have hvolK : ∀ i, volume (A i) ≤ volume (K i) + (ε : ℝ≥0∞) := by
    intro i
    have hsub : K₀ i ⊆ K i := by
      intro x hx
      simp only [K, mem_iUnion]
      exact ⟨i, Finset.mem_Ici.mpr le_rfl, Or.inl hx⟩
    exact (hK₀ε i).le.trans (add_le_add (measure_mono hsub) le_rfl)
  have hvolL : ∀ i, volume (B i) ≤ volume (L i) + (ε : ℝ≥0∞) := by
    intro i
    have hsub : L₀ i ⊆ L i := by
      intro x hx
      simp only [L, mem_iUnion]
      exact ⟨i, Finset.mem_Ici.mpr le_rfl, Or.inl hx⟩
    exact (hL₀ε i).le.trans (add_le_add (measure_mono hsub) le_rfl)
  change δ * ∑ i : Fin N, (a * volume (A i) + b * volume (B i)) ≤ R + (ε : ℝ≥0∞)
  calc
    δ * ∑ i : Fin N, (a * volume (A i) + b * volume (B i)) ≤
        δ * ∑ i : Fin N,
          ((a * volume (K i) + b * volume (L i)) + (ε : ℝ≥0∞)) := by
      apply mul_le_mul_left'
      apply Finset.sum_le_sum
      intro i hi
      calc
          a * volume (A i) + b * volume (B i) ≤
              a * (volume (K i) + (ε : ℝ≥0∞)) +
                b * (volume (L i) + (ε : ℝ≥0∞)) :=
            add_le_add (mul_le_mul_left' (hvolK i) a) (mul_le_mul_left' (hvolL i) b)
          _ = (a * volume (K i) + b * volume (L i)) + (ε : ℝ≥0∞) := by
            rw [mul_add, mul_add]
            calc
              a * volume (K i) + a * (ε : ℝ≥0∞) +
                    (b * volume (L i) + b * (ε : ℝ≥0∞)) =
                  (a * volume (K i) + b * volume (L i)) +
                    (a + b) * (ε : ℝ≥0∞) := by
                rw [add_mul]
                ac_rfl
              _ = _ := by rw [hab, one_mul]
    _ = δ * ∑ i : Fin N, (a * volume (K i) + b * volume (L i)) +
          δ * (N : ℝ≥0∞) * (ε : ℝ≥0∞) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_add]
      simp only [Finset.card_univ, Fintype.card_fin]
      ac_rfl
    _ ≤ R + (ε : ℝ≥0∞) := by
      apply add_le_add hcompact
      have hδ : δ * (N : ℝ≥0∞) ≤ 1 := by
        dsimp only [δ]
        rw [← ENNReal.div_eq_inv_mul]
        apply (ENNReal.div_le_iff (by simp) (by finiteness)).mpr
        simp
      calc
        δ * (N : ℝ≥0∞) * (ε : ℝ≥0∞) ≤ 1 * (ε : ℝ≥0∞) :=
          mul_le_mul_right' hδ _
        _ = (ε : ℝ≥0∞) := one_mul _

theorem finite_grid_solution
    (N : ℕ) (hN : 0 < N)
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (hfsup : sSup (Set.range f) = 1)
    (hgsup : sSup (Set.range g) = 1) :
    ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ *
        ∑ i : Fin N,
          (ENNReal.ofReal (1 - l) * volume
              {x : ℝ | (((i.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ)) ≤ f x} +
            ENNReal.ofReal l * volume
              {y : ℝ | (((i.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ)) ≤ g y}) ≤
      ∫⁻ z, sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
        (1 - l) • x + l • y = z ∧
          q = f x ^ (1 - l) * g y ^ l} := by
  exact grid_tail_sum_le N hN l hl0 hl1 f g hf hg hfc hgc hf1 hg1 hfsup hgsup


private theorem grid_approx_pointwise
    (N : ℕ) (hN : 0 < N) (u : ℝ≥0∞) (hu : u ≤ 1) :
    u ≤ ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ *
        (∑ i : Fin N,
          if (((i.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ)) ≤ u then 1 else 0)
      + ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  let δ : ℝ≥0∞ := ((N + 1 : ℕ) : ℝ≥0∞)⁻¹
  let t : Fin N → ℝ≥0∞ := fun i ↦
    ((i.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ)
  let I : Finset (Fin N) := Finset.univ.filter fun i ↦ t i ≤ u
  have htmono : Monotone t := by
    intro i j hij
    dsimp only [t]
    simp only [ENNReal.div_eq_inv_mul]
    apply mul_le_mul_left'
    exact_mod_cast Nat.succ_le_succ hij
  have hsum : (∑ i : Fin N, if t i ≤ u then 1 else 0) = (I.card : ℝ≥0∞) := by
    rw [Finset.sum_boole]
  rw [show ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ = δ by rfl]
  have htdef (i : Fin N) :
      (((i.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ)) = t i := rfl
  simp_rw [htdef]
  rw [hsum]
  by_cases hI : I.Nonempty
  · let m : Fin N := I.max' hI
    have hmI : m ∈ I := Finset.max'_mem I hI
    have hIeq : I = Finset.Iic m := by
      ext i
      constructor
      · intro hi
        exact Finset.mem_Iic.mpr (Finset.le_max' I i hi)
      · intro hi
        have him : i ≤ m := Finset.mem_Iic.mp hi
        have hmt : t m ≤ u := (Finset.mem_filter.mp hmI).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (htmono him).trans hmt⟩
    have hcard : I.card = m.val + 1 := by
      rw [hIeq, Fin.card_Iic]
    by_cases hlast : m.val + 1 = N
    · calc
        u ≤ 1 := hu
        _ = δ * (I.card : ℝ≥0∞) + δ := by
          rw [hcard, hlast]
          dsimp only [δ]
          have hd : (((N + 1 : ℕ) : ℝ≥0∞)⁻¹ *
              ((N + 1 : ℕ) : ℝ≥0∞)) = 1 := by
            exact ENNReal.inv_mul_cancel (by simp) (by simp)
          calc
            1 = ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ *
                ((N + 1 : ℕ) : ℝ≥0∞) := hd.symm
            _ = ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ * (N : ℝ≥0∞) +
                ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
              push_cast
              ring
    · have hmnext : m.val + 1 < N := Nat.lt_of_le_of_ne m.isLt hlast
      let j : Fin N := ⟨m.val + 1, hmnext⟩
      have hjnot : j ∉ I := by
        intro hj
        have hjm : j ≤ m := Finset.le_max' I j hj
        exact (Nat.not_succ_le_self m.val) hjm
      have hjlt : u < t j := lt_of_not_ge (fun h ↦
        hjnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      calc
        u ≤ t j := hjlt.le
        _ = δ * (I.card : ℝ≥0∞) + δ := by
          rw [hcard]
          dsimp only [t, j, δ]
          rw [ENNReal.div_eq_inv_mul]
          push_cast
          ring
  · have hIz : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    let j : Fin N := ⟨0, hN⟩
    have hjnot : j ∉ I := by simp [hIz]
    have hjlt : u < t j := lt_of_not_ge (fun h ↦
      hjnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    calc
      u ≤ t j := hjlt.le
      _ = δ * (I.card : ℝ≥0∞) + δ := by
        rw [hIz]
        simp only [Finset.card_empty, Nat.cast_zero, mul_zero, zero_add]
        dsimp only [t, j, δ]
        rw [ENNReal.div_eq_inv_mul]
        norm_num

private theorem lintegral_le_grid_add_support_error
    (N : ℕ) (hN : 0 < N)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (hfc : HasCompactSupport f) (hf1 : ∀ x, f x ≤ 1) :
    (∫⁻ x, f x) ≤
      ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ *
          ∑ i : Fin N, volume
            {x : ℝ | (((i.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ)) ≤ f x} +
        ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ * volume (tsupport f) := by
  classical
  let δ : ℝ≥0∞ := ((N + 1 : ℕ) : ℝ≥0∞)⁻¹
  let A : Fin N → Set ℝ := fun i ↦
    {x | (((i.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ)) ≤ f x}
  let F : ℝ → ℝ≥0∞ := fun x ↦
    δ * ∑ i : Fin N, (A i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x
  let E : ℝ → ℝ≥0∞ :=
    (tsupport f).indicator (fun _ ↦ δ)
  have hAm : ∀ i, MeasurableSet (A i) := by
    intro i
    exact measurableSet_le measurable_const hf
  have hFmeas : Measurable F := by
    dsimp only [F]
    exact measurable_const.mul
      (Finset.measurable_sum _ fun i _ ↦ measurable_const.indicator (hAm i))
  have hEle : (∫⁻ x, E x) = δ * volume (tsupport f) := by
    exact lintegral_indicator_const hfc.measurableSet δ
  have hFle : f ≤ fun x ↦ F x + E x := by
    intro x
    by_cases hx : x ∈ tsupport f
    · have hp := grid_approx_pointwise N hN (f x) (hf1 x)
      simpa only [F, E, Set.indicator_of_mem hx, A, Set.indicator, Set.mem_setOf_eq]
        using hp
    · have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [F, E, A, hx, hfx]
  calc
    (∫⁻ x, f x) ≤ ∫⁻ x, F x + E x := lintegral_mono hFle
    _ = (∫⁻ x, F x) + ∫⁻ x, E x := lintegral_add_left hFmeas E
    _ = δ * ∑ i : Fin N, volume (A i) + δ * volume (tsupport f) := by
      rw [hEle]
      have hδtop : δ ≠ ∞ := by
        dsimp only [δ]
        finiteness
      rw [show (∫⁻ x, F x) = δ * (∫⁻ x,
          ∑ i : Fin N, (A i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x) by
        simpa only [F] using
          lintegral_const_mul' δ
            (fun x ↦ ∑ i : Fin N,
              (A i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x) hδtop]
      rw [lintegral_finsetSum]
      · congr 2
        apply Finset.sum_congr rfl
        intro i hi
        exact lintegral_indicator_one (hAm i)
      · intro i hi
        exact measurable_const.indicator (hAm i)
    _ = _ := by rfl

theorem solution
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (hfsup : sSup (Set.range f) = 1)
    (hgsup : sSup (Set.range g) = 1)
    (hmajor : ∀ x y : ℝ,
      f x ^ (1 - l) * g y ^ l ≤ h ((1 - l) • x + l • y)) :
    ENNReal.ofReal (1 - l) * (∫⁻ x, f x) +
        ENNReal.ofReal l * (∫⁻ x, g x) ≤
      ∫⁻ z, h z := by
  let a : ℝ≥0∞ := ENNReal.ofReal (1 - l)
  let b : ℝ≥0∞ := ENNReal.ofReal l
  let R : ℝ≥0∞ := ∫⁻ z, sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
    (1 - l) • x + l • y = z ∧
      q = f x ^ (1 - l) * g y ^ l}
  have hRtop : R < ∞ :=
    envelope_lintegral_lt_top l hl0 hl1 f g hfc hgc hf1 hg1
  have hcore : a * (∫⁻ x, f x) + b * (∫⁻ x, g x) ≤ R := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε hR
    let C : ℝ≥0∞ :=
      a * volume (tsupport f) + b * volume (tsupport g)
    have hfvoltop : volume (tsupport f) ≠ ∞ := hfc.measure_lt_top.ne
    have hgvoltop : volume (tsupport g) ≠ ∞ := hgc.measure_lt_top.ne
    have hCtop : C ≠ ∞ := by
      dsimp only [C, a, b]
      finiteness
    have hεne : (ε : ℝ≥0∞) ≠ 0 := by exact_mod_cast hε.ne'
    obtain ⟨N, hN, hNerr⟩ :=
      ENNReal.exists_nat_pos_inv_mul_lt hCtop hεne
    let δ : ℝ≥0∞ := ((N + 1 : ℕ) : ℝ≥0∞)⁻¹
    let VF : Fin N → ℝ≥0∞ := fun i ↦ volume
      {x : ℝ | (((i.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ)) ≤ f x}
    let VG : Fin N → ℝ≥0∞ := fun i ↦ volume
      {y : ℝ | (((i.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ)) ≤ g y}
    have hδle : δ ≤ (N : ℝ≥0∞)⁻¹ := by
      dsimp only [δ]
      rw [ENNReal.inv_le_inv]
      exact_mod_cast Nat.le_succ N
    have herr : δ * C ≤ (ε : ℝ≥0∞) := by
      exact (mul_le_mul_right' hδle C).trans hNerr.le
    have hfgrid :
        (∫⁻ x, f x) ≤ δ * ∑ i : Fin N, VF i +
          δ * volume (tsupport f) := by
      simpa only [δ, VF] using
        lintegral_le_grid_add_support_error N hN f hf hfc hf1
    have hggrid :
        (∫⁻ x, g x) ≤ δ * ∑ i : Fin N, VG i +
          δ * volume (tsupport g) := by
      simpa only [δ, VG] using
        lintegral_le_grid_add_support_error N hN g hg hgc hg1
    have hgrid : δ * ∑ i : Fin N, (a * VF i + b * VG i) ≤ R := by
      simpa only [δ, VF, VG, a, b, R] using
        grid_tail_sum_le N hN l hl0 hl1 f g hf hg hfc hgc hf1 hg1 hfsup hgsup
    calc
      a * (∫⁻ x, f x) + b * (∫⁻ x, g x) ≤
          a * (δ * ∑ i : Fin N, VF i + δ * volume (tsupport f)) +
            b * (δ * ∑ i : Fin N, VG i + δ * volume (tsupport g)) :=
        add_le_add (mul_le_mul_left' hfgrid a) (mul_le_mul_left' hggrid b)
      _ = δ * ∑ i : Fin N, (a * VF i + b * VG i) + δ * C := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        dsimp only [C]
        ring
      _ ≤ R + (ε : ℝ≥0∞) := add_le_add hgrid herr
  have hRmajor : R ≤ ∫⁻ z, h z := by
    apply lintegral_mono
    intro z
    apply sSup_le
    intro q hq
    rcases hq with ⟨x, y, hxy, rfl⟩
    rw [← hxy]
    exact hmajor x y
  exact hcore.trans hRmajor
