-- Prove2me | solution 2 for MarkovMixing.evolving_sets_root_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-05T20:19:18.68949+00:00
-- url     : https://prove2.me/submissions/296c8f8a-e3a3-4518-a107-a3419ec3f527

import Definitions.Def_mm_martingale
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Finset MeasureTheory

set_option linter.unusedSectionVars false

namespace P2M

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The clamped threshold function `f y = min 1 (max 0 (Q(S,y)/π y))`. -/
noncomputable def fs (P : Matrix V V ℝ) (π : V → ℝ) (S : Finset V) (y : V) : ℝ :=
  min 1 (max 0 (MarkovMixing.esThresh P π S y))

/-- The superlevel set `L u = {y : f y ≥ u}`. -/
noncomputable def Lv (P : Matrix V V ℝ) (π : V → ℝ) (S : Finset V) (u : ℝ) : Finset V :=
  Finset.univ.filter (fun y => u ≤ fs P π S y)

variable {P : Matrix V V ℝ} {π : V → ℝ} {S : Finset V}

lemma fs_nonneg (y : V) : 0 ≤ fs P π S y := by
  unfold fs
  have : (0:ℝ) ≤ max 0 (MarkovMixing.esThresh P π S y) := le_max_left _ _
  exact le_min zero_le_one this

lemma fs_le_one (y : V) : fs P π S y ≤ 1 := min_le_left _ _

lemma mem_Lv {u : ℝ} {y : V} : y ∈ Lv P π S u ↔ u ≤ fs P π S y := by
  simp [Lv]

lemma esUpper_eq_inf' (T : Finset V) (h : T.Nonempty) :
    MarkovMixing.esUpper P π S T = T.inf' h (fun y => fs P π S y) := by
  unfold MarkovMixing.esUpper fs
  rw [dif_pos h]

lemma esUpper_empty : MarkovMixing.esUpper P π S ∅ = 1 := by
  unfold MarkovMixing.esUpper
  rw [dif_neg]
  simp

lemma esLower_eq_sup' (T : Finset V) (h : Tᶜ.Nonempty) :
    MarkovMixing.esLower P π S T = Tᶜ.sup' h (fun y => fs P π S y) := by
  unfold MarkovMixing.esLower fs
  rw [dif_pos h]

lemma esLower_univ : MarkovMixing.esLower P π S Finset.univ = 0 := by
  unfold MarkovMixing.esLower
  rw [dif_neg]
  simp

lemma esUpper_le_one (T : Finset V) : MarkovMixing.esUpper P π S T ≤ 1 := by
  by_cases h : T.Nonempty
  · rw [esUpper_eq_inf' T h]
    obtain ⟨y, hy⟩ := h
    exact le_trans (Finset.inf'_le _ hy) (fs_le_one y)
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    rw [esUpper_empty]

lemma esLower_nonneg (T : Finset V) : 0 ≤ MarkovMixing.esLower P π S T := by
  by_cases h : Tᶜ.Nonempty
  · rw [esLower_eq_sup' T h]
    obtain ⟨y, hy⟩ := h
    exact le_trans (fs_nonneg y) (Finset.le_sup' _ hy)
  · rw [Finset.not_nonempty_iff_eq_empty, Finset.compl_eq_empty_iff] at h
    subst h
    rw [esLower_univ]

/-- If `u` lies in the interval attached to `T`, then `T` is the superlevel set at `u`. -/
lemma Lv_eq_of_mem_Ioc {u : ℝ} {T : Finset V}
    (hu : u ∈ Set.Ioc (MarkovMixing.esLower P π S T) (MarkovMixing.esUpper P π S T)) :
    Lv P π S u = T := by
  obtain ⟨hlo, hhi⟩ := hu
  ext y
  rw [mem_Lv]
  constructor
  · intro hy
    by_contra hyT
    have hc : Tᶜ.Nonempty := ⟨y, by simpa using hyT⟩
    rw [esLower_eq_sup' T hc] at hlo
    have : fs P π S y ≤ Tᶜ.sup' hc (fun z => fs P π S z) :=
      Finset.le_sup' _ (by simpa using hyT)
    linarith
  · intro hy
    have hT : T.Nonempty := ⟨y, hy⟩
    rw [esUpper_eq_inf' T hT] at hhi
    exact le_trans hhi (Finset.inf'_le _ hy)

/-- Conversely, if `T` is the superlevel set at `u ∈ (0,1]`, then `u` lies in `T`'s interval. -/
lemma mem_Ioc_of_Lv_eq {u : ℝ} {T : Finset V} (hu0 : 0 < u) (hu1 : u ≤ 1)
    (h : Lv P π S u = T) :
    u ∈ Set.Ioc (MarkovMixing.esLower P π S T) (MarkovMixing.esUpper P π S T) := by
  constructor
  · by_cases hc : Tᶜ.Nonempty
    · rw [esLower_eq_sup' T hc, Finset.sup'_lt_iff]
      intro y hy
      have hyT : y ∉ T := by simpa using hy
      rw [← h, mem_Lv] at hyT
      exact lt_of_not_ge hyT
    · rw [Finset.not_nonempty_iff_eq_empty, Finset.compl_eq_empty_iff] at hc
      subst hc
      rw [esLower_univ]
      exact hu0
  · by_cases hT : T.Nonempty
    · rw [esUpper_eq_inf' T hT, Finset.le_inf'_iff]
      intro y hy
      rw [← h, mem_Lv] at hy
      exact hy
    · rw [Finset.not_nonempty_iff_eq_empty] at hT
      subst hT
      rw [esUpper_empty]
      exact hu1


lemma weight_nonneg (T : Finset V) : 0 ≤ MarkovMixing.evolvingSets P π S T :=
  le_max_left _ _

lemma vol_interval (T : Finset V) :
    volume (Set.Ioc (MarkovMixing.esLower P π S T) (MarkovMixing.esUpper P π S T))
      = ENNReal.ofReal (MarkovMixing.evolvingSets P π S T) := by
  rw [Real.volume_Ioc]
  unfold MarkovMixing.evolvingSets
  rcases le_total (MarkovMixing.esUpper P π S T - MarkovMixing.esLower P π S T) 0 with h | h
  · rw [max_eq_left h, ENNReal.ofReal_eq_zero.2 h, ENNReal.ofReal_zero]
  · rw [max_eq_right h]

/-- The master counting tool: the total weight of a family of sets equals the
length of the corresponding set of levels. -/
lemma sum_weights (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (𝒯 : Finset (Finset V))
    (h : ∀ u : ℝ, 0 < u → u ≤ 1 → (Lv P π S u ∈ 𝒯 ↔ u ≤ c)) :
    ∑ T ∈ 𝒯, MarkovMixing.evolvingSets P π S T = c := by
  set I : Finset V → Set ℝ :=
    fun T => Set.Ioc (MarkovMixing.esLower P π S T) (MarkovMixing.esUpper P π S T) with hI
  have key : (⋃ T ∈ 𝒯, I T) = Set.Ioc (0:ℝ) c := by
    ext u
    simp only [Set.mem_iUnion, Set.mem_Ioc, hI, exists_prop]
    constructor
    · rintro ⟨T, hT, hu⟩
      have hL : Lv P π S u = T := Lv_eq_of_mem_Ioc (Set.mem_Ioc.2 hu)
      have h0 : 0 < u := lt_of_le_of_lt (esLower_nonneg T) hu.1
      have h1 : u ≤ 1 := le_trans hu.2 (esUpper_le_one T)
      exact ⟨h0, (h u h0 h1).1 (by rw [hL]; exact hT)⟩
    · rintro ⟨h0, hcu⟩
      have h1 : u ≤ 1 := le_trans hcu hc1
      exact ⟨Lv P π S u, (h u h0 h1).2 hcu,
        Set.mem_Ioc.1 (mem_Ioc_of_Lv_eq h0 h1 rfl)⟩
  have hdisj : ((𝒯 : Set (Finset V))).PairwiseDisjoint I := by
    intro T _ T' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro u huT huT'
    exact hne ((Lv_eq_of_mem_Ioc huT).symm.trans (Lv_eq_of_mem_Ioc huT'))
  have hmeas : ∀ T ∈ 𝒯, MeasurableSet (I T) := fun T _ => measurableSet_Ioc
  have hsum := measure_biUnion_finset (μ := (volume : Measure ℝ)) hdisj hmeas
  rw [key, Real.volume_Ioc, sub_zero] at hsum
  have hsum2 : ENNReal.ofReal c
      = ENNReal.ofReal (∑ T ∈ 𝒯, MarkovMixing.evolvingSets P π S T) := by
    rw [hsum, ENNReal.ofReal_sum_of_nonneg (fun T _ => weight_nonneg T)]
    exact Finset.sum_congr rfl (fun T _ => vol_interval T)
  have := (ENNReal.ofReal_eq_ofReal_iff hc0
    (Finset.sum_nonneg (fun T _ => weight_nonneg T))).1 hsum2
  exact this.symm

section Chain

variable {P : Matrix V V ℝ} {π : V → ℝ} {S : Finset V}

lemma stat_col (hπ : MarkovMixing.IsStationary P π) (y : V) : ∑ x, π x * P x y = π y := by
  have h := congrFun hπ.2 y
  simpa [Matrix.vecMul, dotProduct] using h

lemma Q_nonneg (hP : MarkovMixing.IsStochastic P) (hπ : MarkovMixing.IsStationary P π)
    (y : V) : 0 ≤ ∑ x ∈ S, π x * P x y :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hπ.1.1 x) (hP.1 x y)

lemma Q_le (hP : MarkovMixing.IsStochastic P) (hπ : MarkovMixing.IsStationary P π)
    (y : V) : ∑ x ∈ S, π x * P x y ≤ π y := by
  rw [← stat_col hπ y]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun x _ _ => mul_nonneg (hπ.1.1 x) (hP.1 x y))

lemma fs_eq (hP : MarkovMixing.IsStochastic P) (hπ : MarkovMixing.IsStationary P π)
    (hpos : ∀ x : V, 0 < π x) (y : V) :
    fs P π S y = (∑ x ∈ S, π x * P x y) / π y := by
  unfold fs MarkovMixing.esThresh
  have h0 : 0 ≤ (∑ x ∈ S, π x * P x y) / π y :=
    div_nonneg (Q_nonneg hP hπ y) (hpos y).le
  have h1 : (∑ x ∈ S, π x * P x y) / π y ≤ 1 := (div_le_one (hpos y)).2 (Q_le hP hπ y)
  rw [max_eq_right h0, min_eq_right h1]

lemma pi_mul_fs (hP : MarkovMixing.IsStochastic P) (hπ : MarkovMixing.IsStationary P π)
    (hpos : ∀ x : V, 0 < π x) (y : V) :
    π y * fs P π S y = ∑ x ∈ S, π x * P x y := by
  have hne : π y ≠ 0 := ne_of_gt (hpos y)
  rw [fs_eq hP hπ hpos y]
  field_simp

lemma fs_ge_half_of_mem (hP : MarkovMixing.IsStochastic P) (hπ : MarkovMixing.IsStationary P π)
    (hpos : ∀ x : V, 0 < π x) (hlazy : ∀ x : V, 2⁻¹ ≤ P x x) {y : V} (hy : y ∈ S) :
    2⁻¹ ≤ fs P π S y := by
  rw [fs_eq hP hπ hpos y, le_div_iff₀ (hpos y)]
  have hsingle : π y * P y y ≤ ∑ x ∈ S, π x * P x y :=
    Finset.single_le_sum (f := fun x => π x * P x y)
      (fun x _ => mul_nonneg (hπ.1.1 x) (hP.1 x y)) hy
  nlinarith [hpos y, hlazy y]

lemma fs_le_half_of_not_mem (hP : MarkovMixing.IsStochastic P)
    (hπ : MarkovMixing.IsStationary P π)
    (hpos : ∀ x : V, 0 < π x) (hlazy : ∀ x : V, 2⁻¹ ≤ P x x) {y : V} (hy : y ∉ S) :
    fs P π S y ≤ 2⁻¹ := by
  rw [fs_eq hP hπ hpos y, div_le_iff₀ (hpos y)]
  have hS : S ⊆ Finset.univ \ {y} := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
    rintro rfl
    exact hy hx
  have h1 : ∑ x ∈ S, π x * P x y ≤ ∑ x ∈ Finset.univ \ {y}, π x * P x y :=
    Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun x _ _ => mul_nonneg (hπ.1.1 x) (hP.1 x y))
  have h2 : ∑ x ∈ Finset.univ \ {y}, π x * P x y = π y - π y * P y y := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _), stat_col hπ y]
    simp
  rw [h2] at h1
  nlinarith [hpos y, hlazy y]

lemma esUpper_nonneg (T : Finset V) : 0 ≤ MarkovMixing.esUpper P π S T := by
  by_cases h : T.Nonempty
  · rw [esUpper_eq_inf' T h, Finset.le_inf'_iff]
    exact fun y _ => fs_nonneg y
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    rw [esUpper_empty]
    norm_num

lemma half_le_esUpper_self (hP : MarkovMixing.IsStochastic P)
    (hπ : MarkovMixing.IsStationary P π) (hpos : ∀ x : V, 0 < π x)
    (hlazy : ∀ x : V, 2⁻¹ ≤ P x x) :
    2⁻¹ ≤ MarkovMixing.esUpper P π S S := by
  by_cases h : S.Nonempty
  · rw [esUpper_eq_inf' S h, Finset.le_inf'_iff]
    exact fun y hy => fs_ge_half_of_mem hP hπ hpos hlazy hy
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    rw [esUpper_empty]
    norm_num

lemma esLower_self_le_half (hP : MarkovMixing.IsStochastic P)
    (hπ : MarkovMixing.IsStationary P π) (hpos : ∀ x : V, 0 < π x)
    (hlazy : ∀ x : V, 2⁻¹ ≤ P x x) :
    MarkovMixing.esLower P π S S ≤ 2⁻¹ := by
  by_cases h : Sᶜ.Nonempty
  · rw [esLower_eq_sup' S h, Finset.sup'_le_iff]
    intro y hy
    exact fs_le_half_of_not_mem hP hπ hpos hlazy (by simpa using hy)
  · rw [Finset.not_nonempty_iff_eq_empty, Finset.compl_eq_empty_iff] at h
    subst h
    rw [esLower_univ]
    norm_num

lemma sum_all_weights : ∑ T : Finset V, MarkovMixing.evolvingSets P π S T = 1 :=
  sum_weights 1 zero_le_one le_rfl Finset.univ (fun u _ h1 => by simp [h1])

lemma sum_mem_weights (y : V) :
    ∑ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T),
      MarkovMixing.evolvingSets P π S T = fs P π S y := by
  refine sum_weights (fs P π S y) (fs_nonneg y) (fs_le_one y) _ (fun u _ _ => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact mem_Lv

lemma subset_Lv_iff {u : ℝ} (hu1 : u ≤ 1) :
    S ⊆ Lv P π S u ↔ u ≤ MarkovMixing.esUpper P π S S := by
  by_cases h : S.Nonempty
  · rw [esUpper_eq_inf' S h, Finset.le_inf'_iff]
    constructor
    · intro hsub y hy
      exact mem_Lv.1 (hsub hy)
    · intro hall y hy
      exact mem_Lv.2 (hall y hy)
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    simp [esUpper_empty, hu1]

lemma sum_super_weights :
    ∑ T ∈ Finset.univ.filter (fun T : Finset V => S ⊆ T),
      MarkovMixing.evolvingSets P π S T = MarkovMixing.esUpper P π S S := by
  refine sum_weights _ (esUpper_nonneg S) (esUpper_le_one S) _ (fun u _ h1 => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact subset_Lv_iff h1

lemma sum_super_mem_weights (y : V) :
    ∑ T ∈ Finset.univ.filter (fun T : Finset V => S ⊆ T ∧ y ∈ T),
      MarkovMixing.evolvingSets P π S T
      = min (MarkovMixing.esUpper P π S S) (fs P π S y) := by
  refine sum_weights _ (le_min (esUpper_nonneg S) (fs_nonneg y))
    (min_le_right _ _ |>.trans (fs_le_one y)) _ (fun u _ h1 => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, le_min_iff]
  exact and_congr (subset_Lv_iff h1) mem_Lv

lemma sum_weighted (𝒯 : Finset (Finset V)) (g : V → ℝ) :
    ∑ T ∈ 𝒯, MarkovMixing.evolvingSets P π S T * (∑ y ∈ T, g y)
      = ∑ y : V, g y * ∑ T ∈ 𝒯.filter (fun T : Finset V => y ∈ T),
          MarkovMixing.evolvingSets P π S T := by
  have expand : ∀ T : Finset V, (∑ y ∈ T, g y) = ∑ y : V, if y ∈ T then g y else 0 := by
    intro T
    rw [← Finset.sum_filter]
    congr 1
    ext y
    simp
  calc ∑ T ∈ 𝒯, MarkovMixing.evolvingSets P π S T * (∑ y ∈ T, g y)
      = ∑ T ∈ 𝒯, ∑ y : V,
          (if y ∈ T then MarkovMixing.evolvingSets P π S T * g y else 0) := by
        refine Finset.sum_congr rfl (fun T _ => ?_)
        rw [expand T, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        split <;> simp
    _ = ∑ y : V, ∑ T ∈ 𝒯,
          (if y ∈ T then MarkovMixing.evolvingSets P π S T * g y else 0) := Finset.sum_comm
    _ = ∑ y : V, g y * ∑ T ∈ 𝒯.filter (fun T : Finset V => y ∈ T),
          MarkovMixing.evolvingSets P π S T := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun T _ => ?_)
        split <;> ring

end Chain

section Chain2

variable {P : Matrix V V ℝ} {π : V → ℝ} {S : Finset V}

lemma piT_nonneg (hπ : MarkovMixing.IsStationary P π) (T : Finset V) : 0 ≤ ∑ y ∈ T, π y :=
  Finset.sum_nonneg (fun y _ => hπ.1.1 y)

lemma piT_le_one (hπ : MarkovMixing.IsStationary P π) (T : Finset V) : ∑ y ∈ T, π y ≤ 1 := by
  rw [← hπ.1.2]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    (fun y _ _ => hπ.1.1 y)

lemma martingale (hP : MarkovMixing.IsStochastic P) (hπ : MarkovMixing.IsStationary P π)
    (hpos : ∀ x : V, 0 < π x) :
    ∑ T : Finset V, MarkovMixing.evolvingSets P π S T * (∑ y ∈ T, π y) = ∑ x ∈ S, π x := by
  rw [sum_weighted Finset.univ π]
  have h1 : ∀ y : V, π y * ∑ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T),
      MarkovMixing.evolvingSets P π S T = ∑ x ∈ S, π x * P x y := by
    intro y
    rw [sum_mem_weights y]
    exact pi_mul_fs hP hπ hpos y
  rw [Finset.sum_congr rfl (fun y _ => h1 y), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Finset.mul_sum, hP.2 x, mul_one]

lemma super_weighted (hP : MarkovMixing.IsStochastic P) (hπ : MarkovMixing.IsStationary P π)
    (hpos : ∀ x : V, 0 < π x) (hlazy : ∀ x : V, 2⁻¹ ≤ P x x) :
    ∑ T ∈ Finset.univ.filter (fun T : Finset V => S ⊆ T),
        MarkovMixing.evolvingSets P π S T * (∑ y ∈ T, π y)
      = MarkovMixing.esUpper P π S S * (∑ x ∈ S, π x)
        + ∑ y ∈ Sᶜ, π y * fs P π S y := by
  rw [sum_weighted]
  have hfilt : ∀ y : V, (Finset.univ.filter (fun T : Finset V => S ⊆ T)).filter
      (fun T : Finset V => y ∈ T)
      = Finset.univ.filter (fun T : Finset V => S ⊆ T ∧ y ∈ T) := by
    intro y
    rw [Finset.filter_filter]
  have hstep : ∀ y : V, π y * ∑ T ∈ (Finset.univ.filter (fun T : Finset V => S ⊆ T)).filter
      (fun T : Finset V => y ∈ T), MarkovMixing.evolvingSets P π S T
      = π y * min (MarkovMixing.esUpper P π S S) (fs P π S y) := by
    intro y
    rw [hfilt y, sum_super_mem_weights y]
  rw [Finset.sum_congr rfl (fun y _ => hstep y),
    ← Finset.sum_add_sum_compl S (fun y => π y * min (MarkovMixing.esUpper P π S S) (fs P π S y))]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    have hle : MarkovMixing.esUpper P π S S ≤ fs P π S y := by
      rw [esUpper_eq_inf' S ⟨y, hy⟩]
      exact Finset.inf'_le _ hy
    rw [min_eq_left hle]
    ring
  · refine Finset.sum_congr rfl (fun y hy => ?_)
    have hle : fs P π S y ≤ MarkovMixing.esUpper P π S S :=
      le_trans (fs_le_half_of_not_mem hP hπ hpos hlazy (by simpa using hy))
        (half_le_esUpper_self hP hπ hpos hlazy)
    rw [min_eq_right hle]

lemma w_self (hP : MarkovMixing.IsStochastic P) (hπ : MarkovMixing.IsStationary P π)
    (hpos : ∀ x : V, 0 < π x) (hlazy : ∀ x : V, 2⁻¹ ≤ P x x) :
    MarkovMixing.evolvingSets P π S S
      = MarkovMixing.esUpper P π S S - MarkovMixing.esLower P π S S := by
  unfold MarkovMixing.evolvingSets
  apply max_eq_right
  have h1 := half_le_esUpper_self (S := S) hP hπ hpos hlazy
  have h2 := esLower_self_le_half (S := S) hP hπ hpos hlazy
  linarith

end Chain2

/-- The first half-weight: the mass of levels `u ∈ (0, 1/2]`. -/
noncomputable def aw (P : Matrix V V ℝ) (π : V → ℝ) (S T : Finset V) : ℝ :=
  (if T = S then 2⁻¹ - MarkovMixing.esUpper P π S S else 0)
    + (if S ⊆ T then MarkovMixing.evolvingSets P π S T else 0)

/-- The second half-weight: the mass of levels `u ∈ (1/2, 1]`. -/
noncomputable def bw (P : Matrix V V ℝ) (π : V → ℝ) (S T : Finset V) : ℝ :=
  MarkovMixing.evolvingSets P π S T - aw P π S T

section Split

variable {P : Matrix V V ℝ} {π : V → ℝ} {S : Finset V}

lemma aw_nonneg (hP : MarkovMixing.IsStochastic P) (hπ : MarkovMixing.IsStationary P π)
    (hpos : ∀ x : V, 0 < π x) (hlazy : ∀ x : V, 2⁻¹ ≤ P x x)
    (T : Finset V) : 0 ≤ aw P π S T := by
  unfold aw
  by_cases h : T = S
  · subst h
    rw [if_pos rfl, if_pos (Finset.Subset.refl _), w_self hP hπ hpos hlazy]
    have h2 := esLower_self_le_half (S := T) hP hπ hpos hlazy
    linarith
  · rw [if_neg h, zero_add]
    by_cases h2 : S ⊆ T
    · rw [if_pos h2]; exact weight_nonneg T
    · rw [if_neg h2]

lemma bw_nonneg (hP : MarkovMixing.IsStochastic P) (hπ : MarkovMixing.IsStationary P π)
    (hpos : ∀ x : V, 0 < π x) (hlazy : ∀ x : V, 2⁻¹ ≤ P x x)
    (T : Finset V) : 0 ≤ bw P π S T := by
  unfold bw aw
  by_cases h : T = S
  · subst h
    rw [if_pos rfl, if_pos (Finset.Subset.refl _), w_self hP hπ hpos hlazy]
    have h1 := half_le_esUpper_self (S := T) hP hπ hpos hlazy
    linarith
  · rw [if_neg h, zero_add]
    by_cases h2 : S ⊆ T
    · rw [if_pos h2]; simp
    · rw [if_neg h2, sub_zero]; exact weight_nonneg T

lemma sum_aw : ∑ T : Finset V, aw P π S T = 2⁻¹ := by
  unfold aw
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ S
    (fun _ => 2⁻¹ - MarkovMixing.esUpper P π S S), if_pos (Finset.mem_univ S),
    ← Finset.sum_filter, sum_super_weights]
  ring

lemma sum_bw : ∑ T : Finset V, bw P π S T = 2⁻¹ := by
  unfold bw
  rw [Finset.sum_sub_distrib, sum_all_weights, sum_aw]
  norm_num

lemma sum_aw_pi (hP : MarkovMixing.IsStochastic P) (hπ : MarkovMixing.IsStationary P π)
    (hpos : ∀ x : V, 0 < π x) (hlazy : ∀ x : V, 2⁻¹ ≤ P x x) :
    ∑ T : Finset V, aw P π S T * (∑ y ∈ T, π y)
      = 2⁻¹ * (∑ x ∈ S, π x) + ∑ y ∈ Sᶜ, π y * fs P π S y := by
  unfold aw
  have : ∀ T : Finset V,
      ((if T = S then 2⁻¹ - MarkovMixing.esUpper P π S S else 0)
        + (if S ⊆ T then MarkovMixing.evolvingSets P π S T else 0)) * (∑ y ∈ T, π y)
      = (if T = S then (2⁻¹ - MarkovMixing.esUpper P π S S) * (∑ y ∈ T, π y) else 0)
        + (if S ⊆ T then MarkovMixing.evolvingSets P π S T * (∑ y ∈ T, π y) else 0) := by
    intro T
    rw [add_mul]
    congr 1 <;> split <;> simp
  rw [Finset.sum_congr rfl (fun T _ => this T), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ S
      (fun T => (2⁻¹ - MarkovMixing.esUpper P π S S) * (∑ y ∈ T, π y)),
    if_pos (Finset.mem_univ S), ← Finset.sum_filter,
    super_weighted hP hπ hpos hlazy]
  ring

lemma sum_bw_pi (hP : MarkovMixing.IsStochastic P) (hπ : MarkovMixing.IsStationary P π)
    (hpos : ∀ x : V, 0 < π x) (hlazy : ∀ x : V, 2⁻¹ ≤ P x x) :
    ∑ T : Finset V, bw P π S T * (∑ y ∈ T, π y)
      = 2⁻¹ * (∑ x ∈ S, π x) - ∑ y ∈ Sᶜ, π y * fs P π S y := by
  unfold bw
  have : ∀ T : Finset V, (MarkovMixing.evolvingSets P π S T - aw P π S T) * (∑ y ∈ T, π y)
      = MarkovMixing.evolvingSets P π S T * (∑ y ∈ T, π y)
        - aw P π S T * (∑ y ∈ T, π y) := fun T => by ring
  rw [Finset.sum_congr rfl (fun T _ => this T), Finset.sum_sub_distrib,
    martingale hP hπ hpos, sum_aw_pi hP hπ hpos hlazy]
  ring

end Split

lemma cs_bound {ι : Type*} (F : Finset ι) (a v : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hv : ∀ i, 0 ≤ v i) :
    ∑ i ∈ F, a i * Real.sqrt (v i)
      ≤ Real.sqrt (∑ i ∈ F, a i) * Real.sqrt (∑ i ∈ F, a i * v i) := by
  have h := Real.sum_sqrt_mul_sqrt_le (f := a) (g := fun i => a i * v i) F ha
    (fun i => mul_nonneg (ha i) (hv i))
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Real.sqrt_mul (ha i), show a i * (a i * v i) = (a i) ^ 2 * v i by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (ha i)]

lemma core_aux (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (Real.sqrt 2⁻¹ * Real.sqrt A + Real.sqrt 2⁻¹ * Real.sqrt B) ^ 2
      = 2⁻¹ * (A + B) + Real.sqrt (A * B) := by
  have e1 : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA
  have e2 : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB
  have e3 : Real.sqrt (2⁻¹ : ℝ) ^ 2 = (2⁻¹ : ℝ) := Real.sq_sqrt (by norm_num)
  have e4 : Real.sqrt A * Real.sqrt B = Real.sqrt (A * B) := (Real.sqrt_mul hA B).symm
  have expand : (Real.sqrt 2⁻¹ * Real.sqrt A + Real.sqrt 2⁻¹ * Real.sqrt B) ^ 2
      = Real.sqrt (2⁻¹ : ℝ) ^ 2 *
        (Real.sqrt A ^ 2 + Real.sqrt B ^ 2 + 2 * (Real.sqrt A * Real.sqrt B)) := by ring
  rw [expand, e1, e2, e3, e4]
  ring

lemma core (p q t : ℝ) (hp : 0 ≤ p) (hq0 : 0 ≤ q) (hq : 2 * q ≤ p) (ht0 : 0 ≤ t)
    (htq : t * p ≤ q) :
    Real.sqrt 2⁻¹ * Real.sqrt (2⁻¹ * p + q) + Real.sqrt 2⁻¹ * Real.sqrt (2⁻¹ * p - q)
      ≤ (1 - t ^ 2 / 2) * Real.sqrt p := by
  rcases eq_or_lt_of_le hp with hp0 | hp0
  · have hq' : q = 0 := le_antisymm (by linarith) hq0
    rw [← hp0, hq']
    norm_num
  · have ht : t ≤ 2⁻¹ := by nlinarith
    have hA : (0:ℝ) ≤ 2⁻¹ * p + q := by linarith
    have hB : (0:ℝ) ≤ 2⁻¹ * p - q := by linarith
    have ht4 : (0:ℝ) ≤ 1 - 4 * t ^ 2 := by nlinarith
    have ht2 : (0:ℝ) ≤ 1 - 2 * t ^ 2 := by nlinarith
    have hL0 : 0 ≤ Real.sqrt 2⁻¹ * Real.sqrt (2⁻¹ * p + q)
        + Real.sqrt 2⁻¹ * Real.sqrt (2⁻¹ * p - q) := by positivity
    have hLsq := core_aux (2⁻¹ * p + q) (2⁻¹ * p - q) hA hB
    have hq2 : t ^ 2 * p ^ 2 ≤ q ^ 2 := by
      have h := mul_self_le_mul_self (mul_nonneg ht0 hp) htq
      nlinarith [h]
    have hcmp : (2⁻¹ * p + q) * (2⁻¹ * p - q)
        ≤ (2⁻¹ * p * Real.sqrt (1 - 4 * t ^ 2)) ^ 2 := by
      have h2 : Real.sqrt (1 - 4 * t ^ 2) ^ 2 = 1 - 4 * t ^ 2 := Real.sq_sqrt ht4
      have expand : (2⁻¹ * p * Real.sqrt (1 - 4 * t ^ 2)) ^ 2
          = 4⁻¹ * p ^ 2 * (1 - 4 * t ^ 2) := by rw [mul_pow, mul_pow, h2]; ring
      rw [expand]
      nlinarith [hq2]
    have hroot : Real.sqrt ((2⁻¹ * p + q) * (2⁻¹ * p - q))
        ≤ 2⁻¹ * p * Real.sqrt (1 - 4 * t ^ 2) := by
      have hnn : 0 ≤ 2⁻¹ * p * Real.sqrt (1 - 4 * t ^ 2) := by positivity
      calc Real.sqrt ((2⁻¹ * p + q) * (2⁻¹ * p - q))
          ≤ Real.sqrt ((2⁻¹ * p * Real.sqrt (1 - 4 * t ^ 2)) ^ 2) := Real.sqrt_le_sqrt hcmp
        _ = 2⁻¹ * p * Real.sqrt (1 - 4 * t ^ 2) := Real.sqrt_sq hnn
    have hsq_le : Real.sqrt (1 - 4 * t ^ 2) ≤ 1 - 2 * t ^ 2 := by
      have h := Real.sqrt_le_sqrt (show (1 - 4 * t ^ 2) ≤ (1 - 2 * t ^ 2) ^ 2 by nlinarith)
      rwa [Real.sqrt_sq ht2] at h
    have hstep : 2⁻¹ * p * Real.sqrt (1 - 4 * t ^ 2) ≤ 2⁻¹ * p - p * t ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hsq_le (show (0:ℝ) ≤ 2⁻¹ * p by linarith)
      nlinarith [h]
    have hLsq_le : (Real.sqrt 2⁻¹ * Real.sqrt (2⁻¹ * p + q)
        + Real.sqrt 2⁻¹ * Real.sqrt (2⁻¹ * p - q)) ^ 2 ≤ p * (1 - t ^ 2) := by
      rw [hLsq]
      have h := hroot.trans hstep
      nlinarith [h]
    have hRnn : (0:ℝ) ≤ 1 - t ^ 2 / 2 := by nlinarith
    have hRRnn : 0 ≤ (1 - t ^ 2 / 2) * Real.sqrt p := mul_nonneg hRnn (Real.sqrt_nonneg p)
    have hRsq : ((1 - t ^ 2 / 2) * Real.sqrt p) ^ 2 = (1 - t ^ 2 / 2) ^ 2 * p := by
      rw [mul_pow, Real.sq_sqrt hp]
    have hfinal : (Real.sqrt 2⁻¹ * Real.sqrt (2⁻¹ * p + q)
        + Real.sqrt 2⁻¹ * Real.sqrt (2⁻¹ * p - q)) ^ 2
        ≤ ((1 - t ^ 2 / 2) * Real.sqrt p) ^ 2 := by
      rw [hRsq]
      nlinarith [hLsq_le, hp, mul_nonneg hp (pow_nonneg (sq_nonneg t) 2)]
    calc Real.sqrt 2⁻¹ * Real.sqrt (2⁻¹ * p + q) + Real.sqrt 2⁻¹ * Real.sqrt (2⁻¹ * p - q)
        = Real.sqrt ((Real.sqrt 2⁻¹ * Real.sqrt (2⁻¹ * p + q)
            + Real.sqrt 2⁻¹ * Real.sqrt (2⁻¹ * p - q)) ^ 2) := (Real.sqrt_sq hL0).symm
      _ ≤ Real.sqrt (((1 - t ^ 2 / 2) * Real.sqrt p) ^ 2) := Real.sqrt_le_sqrt hfinal
      _ = (1 - t ^ 2 / 2) * Real.sqrt p := Real.sqrt_sq hRRnn

section Final

variable {P : Matrix V V ℝ} {π : V → ℝ} {S : Finset V}

lemma bstar_nonneg (hP : MarkovMixing.IsStochastic P) (hπ : MarkovMixing.IsStationary P π) :
    0 ≤ MarkovMixing.bottleneckStar P π := by
  unfold MarkovMixing.bottleneckStar
  refine Real.iInf_nonneg (fun i => ?_)
  unfold MarkovMixing.bottleneckRatio MarkovMixing.edgeMeasure
  refine div_nonneg (Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ =>
    mul_nonneg (hπ.1.1 x) (hP.1 x y)))) (Finset.sum_nonneg (fun x _ => hπ.1.1 x))

lemma bstar_le {A : Finset V} (hA : A.Nonempty) (hmass : ∑ x ∈ A, π x ≤ 2⁻¹) :
    MarkovMixing.bottleneckStar P π ≤ MarkovMixing.bottleneckRatio P π A :=
  ciInf_le (Finite.bddBelow_range _)
    (⟨A, hA, hmass⟩ : {B : Finset V // B.Nonempty ∧ ∑ x ∈ B, π x ≤ 2⁻¹})

lemma q_eq (hP : MarkovMixing.IsStochastic P) (hπ : MarkovMixing.IsStationary P π)
    (hpos : ∀ x : V, 0 < π x) :
    ∑ y ∈ Sᶜ, π y * fs P π S y = ∑ x ∈ S, ∑ y ∈ Sᶜ, π x * P x y := by
  rw [Finset.sum_congr rfl (fun y (_ : y ∈ Sᶜ) => pi_mul_fs hP hπ hpos y)]
  exact Finset.sum_comm

lemma q_symm (hP : MarkovMixing.IsStochastic P) (hπ : MarkovMixing.IsStationary P π) :
    ∑ x ∈ S, ∑ y ∈ Sᶜ, π x * P x y = ∑ x ∈ Sᶜ, ∑ y ∈ S, π x * P x y := by
  have hrow : ∀ x : V, ∑ y ∈ S, π x * P x y + ∑ y ∈ Sᶜ, π x * P x y = π x := by
    intro x
    rw [Finset.sum_add_sum_compl, ← Finset.mul_sum, hP.2 x, mul_one]
  have hcol : ∀ y : V, ∑ x ∈ S, π x * P x y + ∑ x ∈ Sᶜ, π x * P x y = π y := by
    intro y
    rw [Finset.sum_add_sum_compl]
    exact stat_col hπ y
  have e1 : ∑ x ∈ S, ∑ y ∈ S, π x * P x y + ∑ x ∈ S, ∑ y ∈ Sᶜ, π x * P x y
      = ∑ x ∈ S, π x := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => hrow x)
  have e2 : ∑ y ∈ S, ∑ x ∈ S, π x * P x y + ∑ y ∈ S, ∑ x ∈ Sᶜ, π x * P x y
      = ∑ x ∈ S, π x := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun y _ => hcol y)
  have e3 : ∑ x ∈ S, ∑ y ∈ S, π x * P x y = ∑ y ∈ S, ∑ x ∈ S, π x * P x y := Finset.sum_comm
  have e4 : ∑ y ∈ S, ∑ x ∈ Sᶜ, π x * P x y = ∑ x ∈ Sᶜ, ∑ y ∈ S, π x * P x y := Finset.sum_comm
  linarith

lemma bratio_S (hP : MarkovMixing.IsStochastic P) (hπ : MarkovMixing.IsStationary P π)
    (hpos : ∀ x : V, 0 < π x) :
    MarkovMixing.bottleneckRatio P π S
      = (∑ y ∈ Sᶜ, π y * fs P π S y) / ∑ x ∈ S, π x := by
  rw [q_eq hP hπ hpos]
  rfl

lemma bratio_compl (hP : MarkovMixing.IsStochastic P) (hπ : MarkovMixing.IsStationary P π)
    (hpos : ∀ x : V, 0 < π x) :
    MarkovMixing.bottleneckRatio P π Sᶜ
      = (∑ y ∈ Sᶜ, π y * fs P π S y) / ∑ x ∈ Sᶜ, π x := by
  rw [q_eq hP hπ hpos, q_symm hP hπ]
  unfold MarkovMixing.bottleneckRatio MarkovMixing.edgeMeasure
  rw [compl_compl]

lemma pi_compl (hπ : MarkovMixing.IsStationary P π) :
    ∑ x ∈ Sᶜ, π x = 1 - ∑ x ∈ S, π x := by
  have h := Finset.sum_add_sum_compl S π
  rw [hπ.1.2] at h
  linarith

lemma two_Q_le (hP : MarkovMixing.IsStochastic P) (hπ : MarkovMixing.IsStationary P π)
    (hlazy : ∀ x : V, 2⁻¹ ≤ P x x) (A : Finset V) :
    2 * (∑ x ∈ A, ∑ y ∈ Aᶜ, π x * P x y) ≤ ∑ x ∈ A, π x := by
  have hb : ∀ x ∈ A, ∑ y ∈ Aᶜ, π x * P x y ≤ 2⁻¹ * π x := by
    intro x hx
    rw [← Finset.mul_sum]
    have h1 : ∑ y ∈ A, P x y + ∑ y ∈ Aᶜ, P x y = 1 := by
      rw [Finset.sum_add_sum_compl]
      exact hP.2 x
    have h2 : P x x ≤ ∑ y ∈ A, P x y := Finset.single_le_sum (fun y _ => hP.1 x y) hx
    have h3 : ∑ y ∈ Aᶜ, P x y ≤ 2⁻¹ := by linarith [hlazy x]
    nlinarith [hπ.1.1 x, h3]
  have h := Finset.sum_le_sum hb
  rw [← Finset.mul_sum] at h
  linarith

end Final

theorem main {P : Matrix V V ℝ} (hP : MarkovMixing.IsStochastic P)
    {π : V → ℝ} (hπ : MarkovMixing.IsStationary P π) (hpos : ∀ x : V, 0 < π x)
    (hlazy : ∀ x : V, 2⁻¹ ≤ P x x) (S : Finset V) :
    (∑ T : Finset V, MarkovMixing.evolvingSets P π S T *
      Real.sqrt (min (∑ x ∈ T, π x) (1 - ∑ x ∈ T, π x))) ≤
      (1 - MarkovMixing.bottleneckStar P π ^ 2 / 2) *
        Real.sqrt (min (∑ x ∈ S, π x) (1 - ∑ x ∈ S, π x)) := by
  have hsplit : ∀ T : Finset V,
      MarkovMixing.evolvingSets P π S T *
          Real.sqrt (min (∑ x ∈ T, π x) (1 - ∑ x ∈ T, π x))
        = aw P π S T * Real.sqrt (min (∑ x ∈ T, π x) (1 - ∑ x ∈ T, π x))
          + bw P π S T * Real.sqrt (min (∑ x ∈ T, π x) (1 - ∑ x ∈ T, π x)) := by
    intro T
    unfold bw
    ring
  rw [Finset.sum_congr rfl (fun T _ => hsplit T), Finset.sum_add_distrib]
  have ha : ∀ T : Finset V, 0 ≤ aw P π S T := aw_nonneg hP hπ hpos hlazy
  have hb : ∀ T : Finset V, 0 ≤ bw P π S T := bw_nonneg hP hπ hpos hlazy
  have hq0 : 0 ≤ ∑ y ∈ Sᶜ, π y * fs P π S y :=
    Finset.sum_nonneg (fun y _ => mul_nonneg (hπ.1.1 y) (fs_nonneg y))
  have ht0 : 0 ≤ MarkovMixing.bottleneckStar P π := bstar_nonneg hP hπ
  by_cases hcase : ∑ x ∈ S, π x ≤ 2⁻¹
  · -- the light case: `π(S) ≤ 1/2`, so `π(S♯) = π(S)`
    have hmin : min (∑ x ∈ S, π x) (1 - ∑ x ∈ S, π x) = ∑ x ∈ S, π x :=
      min_eq_left (by linarith)
    have hA : ∑ T : Finset V,
        aw P π S T * Real.sqrt (min (∑ x ∈ T, π x) (1 - ∑ x ∈ T, π x))
        ≤ Real.sqrt 2⁻¹ *
          Real.sqrt (2⁻¹ * (∑ x ∈ S, π x) + ∑ y ∈ Sᶜ, π y * fs P π S y) := by
      calc ∑ T : Finset V, aw P π S T * Real.sqrt (min (∑ x ∈ T, π x) (1 - ∑ x ∈ T, π x))
          ≤ ∑ T : Finset V, aw P π S T * Real.sqrt (∑ x ∈ T, π x) :=
            Finset.sum_le_sum (fun T _ => mul_le_mul_of_nonneg_left
              (Real.sqrt_le_sqrt (min_le_left _ _)) (ha T))
        _ ≤ Real.sqrt (∑ T : Finset V, aw P π S T) *
            Real.sqrt (∑ T : Finset V, aw P π S T * (∑ x ∈ T, π x)) :=
            cs_bound _ _ _ ha (fun T => piT_nonneg hπ T)
        _ = _ := by rw [sum_aw, sum_aw_pi hP hπ hpos hlazy]
    have hB : ∑ T : Finset V,
        bw P π S T * Real.sqrt (min (∑ x ∈ T, π x) (1 - ∑ x ∈ T, π x))
        ≤ Real.sqrt 2⁻¹ *
          Real.sqrt (2⁻¹ * (∑ x ∈ S, π x) - ∑ y ∈ Sᶜ, π y * fs P π S y) := by
      calc ∑ T : Finset V, bw P π S T * Real.sqrt (min (∑ x ∈ T, π x) (1 - ∑ x ∈ T, π x))
          ≤ ∑ T : Finset V, bw P π S T * Real.sqrt (∑ x ∈ T, π x) :=
            Finset.sum_le_sum (fun T _ => mul_le_mul_of_nonneg_left
              (Real.sqrt_le_sqrt (min_le_left _ _)) (hb T))
        _ ≤ Real.sqrt (∑ T : Finset V, bw P π S T) *
            Real.sqrt (∑ T : Finset V, bw P π S T * (∑ x ∈ T, π x)) :=
            cs_bound _ _ _ hb (fun T => piT_nonneg hπ T)
        _ = _ := by rw [sum_bw, sum_bw_pi hP hπ hpos hlazy]
    have hqp : 2 * (∑ y ∈ Sᶜ, π y * fs P π S y) ≤ ∑ x ∈ S, π x := by
      rw [q_eq hP hπ hpos]
      exact two_Q_le hP hπ hlazy S
    have hbs : MarkovMixing.bottleneckStar P π * (∑ x ∈ S, π x)
        ≤ ∑ y ∈ Sᶜ, π y * fs P π S y := by
      rcases Finset.eq_empty_or_nonempty S with hS | hS
      · subst hS
        simp only [Finset.sum_empty, mul_zero]
        exact Finset.sum_nonneg (fun y _ => mul_nonneg (hπ.1.1 y) (fs_nonneg y))
      · have hp0 : 0 < ∑ x ∈ S, π x := Finset.sum_pos (fun x _ => hpos x) hS
        have hle := bstar_le (P := P) (π := π) hS hcase
        rw [bratio_S hP hπ hpos, le_div_iff₀ hp0] at hle
        exact hle
    have hcore := core (∑ x ∈ S, π x) (∑ y ∈ Sᶜ, π y * fs P π S y)
      (MarkovMixing.bottleneckStar P π) (piT_nonneg hπ S) hq0 hqp ht0 hbs
    rw [hmin]
    linarith
  · -- the heavy case: `π(S) > 1/2`, so `π(S♯) = 1 − π(S)`
    replace hcase : 2⁻¹ < ∑ x ∈ S, π x := lt_of_not_ge hcase
    have hmin : min (∑ x ∈ S, π x) (1 - ∑ x ∈ S, π x) = 1 - ∑ x ∈ S, π x :=
      min_eq_right (by linarith)
    have hcompl : ∀ T : Finset V, 0 ≤ 1 - ∑ x ∈ T, π x := fun T => by
      linarith [piT_le_one hπ T]
    have hsum_aw' : ∑ T : Finset V, aw P π S T * (1 - ∑ x ∈ T, π x)
        = 2⁻¹ * (1 - ∑ x ∈ S, π x) - ∑ y ∈ Sᶜ, π y * fs P π S y := by
      have e : ∀ T : Finset V, aw P π S T * (1 - ∑ x ∈ T, π x)
          = aw P π S T - aw P π S T * (∑ x ∈ T, π x) := fun T => by ring
      rw [Finset.sum_congr rfl (fun T _ => e T), Finset.sum_sub_distrib, sum_aw,
        sum_aw_pi hP hπ hpos hlazy]
      ring
    have hsum_bw' : ∑ T : Finset V, bw P π S T * (1 - ∑ x ∈ T, π x)
        = 2⁻¹ * (1 - ∑ x ∈ S, π x) + ∑ y ∈ Sᶜ, π y * fs P π S y := by
      have e : ∀ T : Finset V, bw P π S T * (1 - ∑ x ∈ T, π x)
          = bw P π S T - bw P π S T * (∑ x ∈ T, π x) := fun T => by ring
      rw [Finset.sum_congr rfl (fun T _ => e T), Finset.sum_sub_distrib, sum_bw,
        sum_bw_pi hP hπ hpos hlazy]
      ring
    have hA : ∑ T : Finset V,
        aw P π S T * Real.sqrt (min (∑ x ∈ T, π x) (1 - ∑ x ∈ T, π x))
        ≤ Real.sqrt 2⁻¹ *
          Real.sqrt (2⁻¹ * (1 - ∑ x ∈ S, π x) - ∑ y ∈ Sᶜ, π y * fs P π S y) := by
      calc ∑ T : Finset V, aw P π S T * Real.sqrt (min (∑ x ∈ T, π x) (1 - ∑ x ∈ T, π x))
          ≤ ∑ T : Finset V, aw P π S T * Real.sqrt (1 - ∑ x ∈ T, π x) :=
            Finset.sum_le_sum (fun T _ => mul_le_mul_of_nonneg_left
              (Real.sqrt_le_sqrt (min_le_right _ _)) (ha T))
        _ ≤ Real.sqrt (∑ T : Finset V, aw P π S T) *
            Real.sqrt (∑ T : Finset V, aw P π S T * (1 - ∑ x ∈ T, π x)) :=
            cs_bound _ _ _ ha hcompl
        _ = _ := by rw [sum_aw, hsum_aw']
    have hB : ∑ T : Finset V,
        bw P π S T * Real.sqrt (min (∑ x ∈ T, π x) (1 - ∑ x ∈ T, π x))
        ≤ Real.sqrt 2⁻¹ *
          Real.sqrt (2⁻¹ * (1 - ∑ x ∈ S, π x) + ∑ y ∈ Sᶜ, π y * fs P π S y) := by
      calc ∑ T : Finset V, bw P π S T * Real.sqrt (min (∑ x ∈ T, π x) (1 - ∑ x ∈ T, π x))
          ≤ ∑ T : Finset V, bw P π S T * Real.sqrt (1 - ∑ x ∈ T, π x) :=
            Finset.sum_le_sum (fun T _ => mul_le_mul_of_nonneg_left
              (Real.sqrt_le_sqrt (min_le_right _ _)) (hb T))
        _ ≤ Real.sqrt (∑ T : Finset V, bw P π S T) *
            Real.sqrt (∑ T : Finset V, bw P π S T * (1 - ∑ x ∈ T, π x)) :=
            cs_bound _ _ _ hb hcompl
        _ = _ := by rw [sum_bw, hsum_bw']
    have hqp : 2 * (∑ y ∈ Sᶜ, π y * fs P π S y) ≤ 1 - ∑ x ∈ S, π x := by
      rw [q_eq hP hπ hpos, q_symm hP hπ, ← pi_compl hπ]
      have h := two_Q_le hP hπ hlazy Sᶜ
      rwa [compl_compl] at h
    have hbs : MarkovMixing.bottleneckStar P π * (1 - ∑ x ∈ S, π x)
        ≤ ∑ y ∈ Sᶜ, π y * fs P π S y := by
      rcases Finset.eq_empty_or_nonempty (Sᶜ) with hS | hS
      · have h0 : (1:ℝ) - ∑ x ∈ S, π x = 0 := by
          rw [← pi_compl hπ, hS, Finset.sum_empty]
        rw [h0, mul_zero]
        exact hq0
      · have hmass : ∑ x ∈ Sᶜ, π x ≤ 2⁻¹ := by
          rw [pi_compl hπ]
          linarith
        have hp0 : 0 < ∑ x ∈ Sᶜ, π x := Finset.sum_pos (fun x _ => hpos x) hS
        have hle := bstar_le (P := P) (π := π) hS hmass
        rw [bratio_compl hP hπ hpos, le_div_iff₀ hp0, pi_compl hπ] at hle
        exact hle
    have hcore := core (1 - ∑ x ∈ S, π x) (∑ y ∈ Sᶜ, π y * fs P π S y)
      (MarkovMixing.bottleneckStar P π) (hcompl S) hq0 hqp ht0 hbs
    rw [hmin]
    linarith

end P2M

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary P π) (hpos : ∀ x : V, 0 < π x)
    (hlazy : ∀ x : V, 2⁻¹ ≤ P x x) (S : Finset V) :
    (∑ T : Finset V, MarkovMixing.evolvingSets P π S T *
      Real.sqrt (min (∑ x ∈ T, π x) (1 - ∑ x ∈ T, π x))) ≤
      (1 - MarkovMixing.bottleneckStar P π ^ 2 / 2) *
        Real.sqrt (min (∑ x ∈ S, π x) (1 - ∑ x ∈ S, π x)) :=
  P2M.main hP hπ hpos hlazy S
