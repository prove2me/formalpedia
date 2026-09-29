-- Prove2me | solution 1 for MarkovMixing.evolving_sets_identity
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T18:16:32.903197+00:00
-- url     : https://prove2.me/submissions/26e7a008-e9dc-42cf-b380-cf03d2708615

import Definitions.Def_mm_martingale
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Recovering `P^t` from the evolving-set process (LPW Lemma 17.12)

The identity `π(x) P^t(x,y) = π(y) P_{{x}}{y ∈ S_t}` is proved by induction on
`t`.  The inductive step needs exactly one fact about a single evolving-set
step, namely the *column identity*

`π(y) ∑_{T ∋ y} P_ES(S,T) = ∑_{z ∈ S} π(z) P(z,y)`,

i.e. the chance that `y` survives into the next set is `Q(S,y)/π(y)`.  That is
proved as in Lemma 17.13: the transition probability `P_ES(S,T)` is the length
of the interval of uniform thresholds whose superlevel set is `T`, those
intervals are pairwise disjoint, and the ones belonging to sets containing `y`
cover `(0, Q(S,y)/π(y)]`.
-/

namespace MarkovMixing

open scoped BigOperators

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

/-- The column identity for one evolving-set step. -/
private lemma es_col {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (hπ : IsStationary P π) (hpos : ∀ x : V, 0 < π x) (S : Finset V) (y : V) :
    π y * ∑ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T), evolvingSets P π S T
      = ∑ z ∈ S, π z * P z y := by
  classical
  have hf0 : ∀ z : V, 0 ≤ min 1 (max 0 (esThresh P π S z)) :=
    fun _ => le_min zero_le_one (le_max_left _ _)
  have hev : ∀ T : Finset V, evolvingSets P π S T
      = max 0 (lvlU (fun z : V => min 1 (max 0 (esThresh P π S z))) T
               - lvlL (fun z : V => min 1 (max 0 (esThresh P π S z))) T) := fun _ => rfl
  have hcol : ∑ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T), evolvingSets P π S T
      = min 1 (max 0 (esThresh P π S y)) := by
    rw [Finset.sum_congr rfl fun T _ => hev T]
    exact lvl_col_sum _ hf0 y
  have hQ0 : 0 ≤ ∑ z ∈ S, π z * P z y :=
    Finset.sum_nonneg fun z _ => mul_nonneg (le_of_lt (hpos z)) (hP.1 z y)
  have hQle : ∑ z ∈ S, π z * P z y ≤ π y := by
    have hsub : ∑ z ∈ S, π z * P z y ≤ ∑ z : V, π z * P z y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun z _ _ => mul_nonneg (le_of_lt (hpos z)) (hP.1 z y))
    have hstat : ∑ z : V, π z * P z y = π y := by
      have h := congrFun hπ.2 y
      simpa [Matrix.vecMul, dotProduct] using h
    linarith
  have hπy : (0 : ℝ) < π y := hpos y
  have hne : π y ≠ 0 := ne_of_gt hπy
  have h1 : max 0 (esThresh P π S y) = esThresh P π S y :=
    max_eq_right (div_nonneg hQ0 (le_of_lt hπy))
  have h2 : min 1 (esThresh P π S y) = esThresh P π S y := by
    refine min_eq_right ?_
    rw [esThresh, div_le_one hπy]
    exact hQle
  rw [hcol, h1, h2, esThresh]
  field_simp

/-- Swapping a sum over subsets against a sum over elements. -/
private lemma subset_sum_swap {V : Type*} [Fintype V] [DecidableEq V]
    (A : Finset V → ℝ) (c : V → ℝ) :
    ∑ S : Finset V, A S * (∑ z ∈ S, c z)
      = ∑ z : V, c z * ∑ S ∈ Finset.univ.filter (fun S : Finset V => z ∈ S), A S := by
  classical
  have step1 : ∀ S : Finset V, A S * (∑ z ∈ S, c z)
      = ∑ z : V, (if z ∈ S then A S * c z else 0) := by
    intro S
    rw [Finset.mul_sum, ← Finset.sum_filter]
    congr 1
    ext z
    simp
  calc ∑ S : Finset V, A S * (∑ z ∈ S, c z)
      = ∑ S : Finset V, ∑ z : V, (if z ∈ S then A S * c z else 0) :=
        Finset.sum_congr rfl fun S _ => step1 S
    _ = ∑ z : V, ∑ S : Finset V, (if z ∈ S then A S * c z else 0) := Finset.sum_comm
    _ = ∑ z : V, c z * ∑ S ∈ Finset.univ.filter (fun S : Finset V => z ∈ S), A S := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [← Finset.sum_filter, Finset.mul_sum]
        exact Finset.sum_congr rfl fun S _ => mul_comm _ _

private lemma es_pow_key {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (hπ : IsStationary P π) (hpos : ∀ x : V, 0 < π x) (x : V) (t : ℕ) :
    ∀ y : V, π x * ((P ^ t) x y)
      = π y * ∑ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T),
          ((evolvingSets P π) ^ t) {x} T := by
  classical
  induction t with
  | zero =>
      intro y
      have h0 : ∑ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T),
          ((evolvingSets P π) ^ 0) ({x} : Finset V) T
          = if y ∈ ({x} : Finset V) then (1 : ℝ) else 0 := by
        simp only [pow_zero, Matrix.one_apply]
        rw [Finset.sum_ite_eq (Finset.univ.filter (fun T : Finset V => y ∈ T))
          ({x} : Finset V) (fun _ => (1 : ℝ))]
        simp
      rw [h0]
      simp only [pow_zero, Matrix.one_apply, Finset.mem_singleton]
      by_cases h : y = x
      · subst h; simp
      · simp [h, Ne.symm h]
  | succ n ih =>
      intro y
      have hpow : ∀ T : Finset V, ((evolvingSets P π) ^ (n + 1)) ({x} : Finset V) T
          = ∑ S : Finset V, ((evolvingSets P π) ^ n) ({x} : Finset V) S
              * evolvingSets P π S T := by
        intro T
        rw [pow_succ]
        simp [Matrix.mul_apply]
      have e1 : π y * ∑ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T),
            ((evolvingSets P π) ^ (n + 1)) ({x} : Finset V) T
          = ∑ S : Finset V, ((evolvingSets P π) ^ n) ({x} : Finset V) S
              * (∑ z ∈ S, π z * P z y) := by
        rw [Finset.sum_congr rfl fun T _ => hpow T]
        rw [Finset.sum_comm]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [← Finset.mul_sum, ← es_col P hP π hπ hpos S y]
        ring
      rw [e1, subset_sum_swap]
      have e2 : ∀ z : V, (π z * P z y) *
            ∑ S ∈ Finset.univ.filter (fun S : Finset V => z ∈ S),
              ((evolvingSets P π) ^ n) ({x} : Finset V) S
          = P z y * (π x * ((P ^ n) x z)) := by
        intro z
        rw [ih z]
        ring
      rw [Finset.sum_congr rfl fun z _ => e2 z]
      rw [pow_succ, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring

end MarkovMixing

open MarkovMixing

/-- **Lemma 17.12** (LPW). -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsStationary P π) (hpos : ∀ x : V, 0 < π x)
    (x y : V) (t : ℕ) :
    (P ^ t) x y = π y / π x *
      ∑ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T),
        ((evolvingSets P π) ^ t) {x} T := by
  have hx : π x ≠ 0 := ne_of_gt (hpos x)
  have hkey := es_pow_key P hP π hπ hpos x t y
  field_simp
  linarith [hkey]
