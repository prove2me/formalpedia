-- Prove2me | solution 1 for MarkovMixing.evolving_sets_martingale
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T18:14:12.39828+00:00
-- url     : https://prove2.me/submissions/50f1b583-b645-4a8e-974f-137ba3976aaa

import Definitions.Def_mm_martingale
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# `π(S_t)` is a martingale for the evolving-set process (LPW Lemma 17.13)

The whole content is the single-step identity
`∑_T P_{ES}(S,T) π(T) = π(S)`, since the process `M_t(ω) = π(ω_t)` depends on
the trajectory only through its last coordinate.

Write `f(y) = min 1 (max 0 (Q(S,y)/π(y)))`.  By construction the transition
probability `P_{ES}(S,T)` is `(U(T) − L(T))⁺`, where `U(T) = min_{y∈T} f(y)`
and `L(T) = max_{y∉T} f(y)`; that is, the length of the interval of thresholds
`u` whose superlevel set `{z : f(z) ≥ u}` is exactly `T`.  Those intervals
`(L(T), U(T)]` are pairwise disjoint and, among the `T` containing a fixed
`y`, they cover exactly `(0, f(y)]`.  Lebesgue measure therefore gives the
column identity `∑_{T ∋ y} P_{ES}(S,T) = f(y)`, and summing against `π`
finishes the proof, because `0 ≤ Q(S,y) ≤ π(y)` makes `f(y) = Q(S,y)/π(y)`.
-/

namespace MarkovMixing

open scoped BigOperators

/-- The upper endpoint of the `u`-interval producing the superlevel set `T`. -/
private noncomputable def lvlU {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → ℝ) (T : Finset V) : ℝ :=
  if h : T.Nonempty then T.inf' h f else 1

/-- The lower endpoint of the `u`-interval producing the superlevel set `T`. -/
private noncomputable def lvlL {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → ℝ) (T : Finset V) : ℝ :=
  if h : Tᶜ.Nonempty then Tᶜ.sup' h f else 0

private lemma lvlU_le {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ)
    {T : Finset V} {y : V} (hy : y ∈ T) : lvlU f T ≤ f y := by
  rw [lvlU, dif_pos ⟨y, hy⟩]
  exact Finset.inf'_le f hy

private lemma le_lvlL {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ)
    {T : Finset V} {y : V} (hy : y ∈ Tᶜ) : f y ≤ lvlL f T := by
  rw [lvlL, dif_pos ⟨y, hy⟩]
  exact Finset.le_sup' f hy

private lemma lvlL_nonneg {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ)
    (hf0 : ∀ z : V, 0 ≤ f z) (T : Finset V) : 0 ≤ lvlL f T := by
  rw [lvlL]
  split
  · rename_i h
    obtain ⟨z, hz⟩ := h
    exact le_trans (hf0 z) (Finset.le_sup' f hz)
  · exact le_refl 0

private lemma lvl_union {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ)
    (hf0 : ∀ z : V, 0 ≤ f z) (y : V) :
    (⋃ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T),
      Set.Ioc (lvlL f T) (lvlU f T)) = Set.Ioc 0 (f y) := by
  classical
  ext u
  simp only [Set.mem_iUnion, Set.mem_Ioc, Finset.mem_filter, Finset.mem_univ, true_and,
    exists_prop]
  constructor
  · rintro ⟨T, hyT, hlo, hhi⟩
    exact ⟨lt_of_le_of_lt (lvlL_nonneg f hf0 T) hlo, le_trans hhi (lvlU_le f hyT)⟩
  · rintro ⟨hu0, huy⟩
    refine ⟨Finset.univ.filter (fun z : V => u ≤ f z), ?_, ?_, ?_⟩
    · simp [huy]
    · rw [lvlL]
      split
      · rename_i h
        rw [Finset.sup'_lt_iff]
        intro z hz
        simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
          not_le] at hz
        exact hz
      · exact hu0
    · rw [lvlU, dif_pos ⟨y, by simp [huy]⟩]
      refine Finset.le_inf' _ _ ?_
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      exact hz

private lemma lvl_disjoint {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ) (y : V) :
    (↑(Finset.univ.filter (fun T : Finset V => y ∈ T)) : Set (Finset V)).PairwiseDisjoint
      (fun T => Set.Ioc (lvlL f T) (lvlU f T)) := by
  classical
  have key : ∀ (R : Finset V) (u : ℝ), u ∈ Set.Ioc (lvlL f R) (lvlU f R) →
      R = Finset.univ.filter (fun z : V => u ≤ f z) := by
    intro R u hu
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hz
      exact le_trans hu.2 (lvlU_le f hz)
    · intro hz
      by_contra hzR
      have hle : f z ≤ lvlL f R := le_lvlL f (Finset.mem_compl.mpr hzR)
      have := hu.1
      linarith
  intro T _ T' _ hne
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  intro u huT huT'
  exact hne ((key T u huT).trans (key T' u huT').symm)

private lemma lvl_col_sum {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ)
    (hf0 : ∀ z : V, 0 ≤ f z) (y : V) :
    ∑ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T),
      max 0 (lvlU f T - lvlL f T) = f y := by
  classical
  have hm := MeasureTheory.measure_biUnion_finset (μ := MeasureTheory.volume)
    (lvl_disjoint f y) (fun T _ => measurableSet_Ioc)
  rw [lvl_union f hf0 y] at hm
  simp only [Real.volume_Ioc] at hm
  have hto := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_sum (fun T _ => ENNReal.ofReal_ne_top)] at hto
  simp only [ENNReal.toReal_ofReal', sub_zero, max_eq_left (hf0 y)] at hto
  rw [hto]
  exact Finset.sum_congr rfl fun T _ => max_comm _ _

private lemma es_row_sum {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (hπ : IsStationary P π) (hpos : ∀ x : V, 0 < π x) (S : Finset V) :
    ∑ T : Finset V, evolvingSets P π S T * (∑ v ∈ T, π v) = ∑ v ∈ S, π v := by
  classical
  have hf0 : ∀ z : V, 0 ≤ min 1 (max 0 (esThresh P π S z)) :=
    fun _ => le_min zero_le_one (le_max_left _ _)
  have hev : ∀ T : Finset V, evolvingSets P π S T
      = max 0 (lvlU (fun z : V => min 1 (max 0 (esThresh P π S z))) T
               - lvlL (fun z : V => min 1 (max 0 (esThresh P π S z))) T) := fun _ => rfl
  have hcol : ∀ v : V,
      ∑ T ∈ Finset.univ.filter (fun T : Finset V => v ∈ T), evolvingSets P π S T
        = min 1 (max 0 (esThresh P π S v)) := by
    intro v
    rw [Finset.sum_congr rfl fun T _ => hev T]
    exact lvl_col_sum _ hf0 v
  have step1 : ∀ T : Finset V, evolvingSets P π S T * (∑ v ∈ T, π v)
      = ∑ v : V, (if v ∈ T then evolvingSets P π S T * π v else 0) := by
    intro T
    rw [Finset.mul_sum, ← Finset.sum_filter]
    congr 1
    ext v
    simp
  have hswap : ∑ T : Finset V, evolvingSets P π S T * (∑ v ∈ T, π v)
      = ∑ v : V, π v * ∑ T ∈ Finset.univ.filter (fun T : Finset V => v ∈ T),
          evolvingSets P π S T := by
    calc ∑ T : Finset V, evolvingSets P π S T * (∑ v ∈ T, π v)
        = ∑ T : Finset V, ∑ v : V, (if v ∈ T then evolvingSets P π S T * π v else 0) :=
          Finset.sum_congr rfl fun T _ => step1 T
      _ = ∑ v : V, ∑ T : Finset V, (if v ∈ T then evolvingSets P π S T * π v else 0) :=
          Finset.sum_comm
      _ = ∑ v : V, π v * ∑ T ∈ Finset.univ.filter (fun T : Finset V => v ∈ T),
            evolvingSets P π S T := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [← Finset.sum_filter, Finset.mul_sum]
          exact Finset.sum_congr rfl fun T _ => mul_comm _ _
  have hQ0 : ∀ v : V, 0 ≤ ∑ x ∈ S, π x * P x v :=
    fun v => Finset.sum_nonneg fun x _ => mul_nonneg (le_of_lt (hpos x)) (hP.1 x v)
  have hQle : ∀ v : V, ∑ x ∈ S, π x * P x v ≤ π v := by
    intro v
    have hsub : ∑ x ∈ S, π x * P x v ≤ ∑ x : V, π x * P x v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun x _ _ => mul_nonneg (le_of_lt (hpos x)) (hP.1 x v))
    have hstat : ∑ x : V, π x * P x v = π v := by
      have h := congrFun hπ.2 v
      simpa [Matrix.vecMul, dotProduct] using h
    linarith
  have hval : ∀ v : V, π v * min 1 (max 0 (esThresh P π S v)) = ∑ x ∈ S, π x * P x v := by
    intro v
    have hπv : (0 : ℝ) < π v := hpos v
    have hne : π v ≠ 0 := ne_of_gt hπv
    have h1 : max 0 (esThresh P π S v) = esThresh P π S v :=
      max_eq_right (div_nonneg (hQ0 v) (le_of_lt hπv))
    have h2 : min 1 (esThresh P π S v) = esThresh P π S v := by
      refine min_eq_right ?_
      rw [esThresh, div_le_one hπv]
      exact hQle v
    rw [h1, h2, esThresh]
    field_simp
  rw [hswap]
  simp only [hcol, hval]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.mul_sum, hP.2 x, mul_one]

end MarkovMixing

open MarkovMixing

/-- **Lemma 17.13** (LPW): for the evolving-set process, the sequence
`π(S_t)` is a martingale. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsStationary P π) (hpos : ∀ x : V, 0 < π x) :
    IsChainMartingale (evolvingSets P π)
      (fun t ω => ∑ v ∈ ω (Fin.last t), π v) := by
  intro t ω
  simp only [Fin.snoc_last]
  exact es_row_sum P hP π hπ hpos (ω (Fin.last t))
