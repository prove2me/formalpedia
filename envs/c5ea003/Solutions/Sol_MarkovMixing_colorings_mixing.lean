-- Prove2me | solution 1 for MarkovMixing.colorings_mixing
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-23T00:18:27.429519+00:00
-- url     : https://prove2.me/submissions/d02be223-bfa1-48cd-8c16-5d9ba1e2067e

import Definitions.Def_mm_coupling
import Theorems.Thm_MarkovMixing_coupling_bound
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Mixing of the Metropolis chain on proper colorings (LPW Theorem 5.7)
-/

namespace MarkovMixing

noncomputable section
open scoped BigOperators
open Finset

section Colorings

variable {Vv : Type*} [Fintype Vv] [DecidableEq Vv]

/-- The set of vertices where two colorings disagree. -/
private def diffSet {q : ℕ} (x y : Vv → Fin q) : Finset Vv :=
  Finset.univ.filter fun v => x v ≠ y v

private lemma diffSet_comm {q : ℕ} (x y : Vv → Fin q) : diffSet x y = diffSet y x := by
  simp only [diffSet]
  exact Finset.filter_congr fun v _ => by exact ⟨fun h => Ne.symm h, fun h => Ne.symm h⟩

private lemma mem_diffSet {q : ℕ} (x y : Vv → Fin q) (v : Vv) :
    v ∈ diffSet x y ↔ x v ≠ y v := by
  simp [diffSet]

/-- Greedy colouring: a graph with maximal degree `< q` has a proper `q`-colouring. -/
private lemma exists_proper (G : SimpleGraph Vv) [DecidableRel G.Adj] (q : ℕ)
    (hq : G.maxDegree < q) : ∃ c : Vv → Fin q, IsProperColoring G c := by
  classical
  have hq0 : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hq
  have key : ∀ S : Finset Vv, ∃ c : Vv → Fin q,
      ∀ v ∈ S, ∀ w ∈ S, G.Adj v w → c v ≠ c w := by
    intro S
    refine Finset.induction_on S ⟨fun _ => ⟨0, hq0⟩, by simp⟩ ?_
    intro a S ha ih
    obtain ⟨c, hc⟩ := ih
    set F : Finset (Fin q) := (S.filter fun w => G.Adj a w).image c with hF
    have hFcard : F.card < q := by
      have h1 : F.card ≤ (S.filter fun w => G.Adj a w).card := Finset.card_image_le
      have h2 : (S.filter fun w => G.Adj a w) ⊆ G.neighborFinset a := by
        intro w hw
        simp only [Finset.mem_filter] at hw
        exact (SimpleGraph.mem_neighborFinset _ _ _).mpr hw.2
      have h3 : (S.filter fun w => G.Adj a w).card ≤ G.degree a :=
        Finset.card_le_card h2
      have h4 : G.degree a ≤ G.maxDegree := G.degree_le_maxDegree a
      omega
    obtain ⟨k, hk⟩ : ∃ k : Fin q, k ∉ F := by
      by_contra hcon
      push_neg at hcon
      have : (Finset.univ : Finset (Fin q)) ⊆ F := fun k _ => hcon k
      have := Finset.card_le_card this
      simp only [Finset.card_univ, Fintype.card_fin] at this
      omega
    refine ⟨Function.update c a k, ?_⟩
    intro v hv w hw hadj
    have hne : v ≠ w := hadj.ne
    rcases Finset.mem_insert.mp hv with hv1 | hv1
    · subst hv1
      have hw1 : w ∈ S := by
        rcases Finset.mem_insert.mp hw with h | h
        · exact absurd h.symm hne
        · exact h
      have hwa : w ≠ v := Ne.symm hne
      rw [Function.update_self, Function.update_of_ne hwa]
      intro hcon
      refine hk ?_
      rw [hF]
      exact Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨hw1, hadj⟩, hcon.symm⟩
    · rcases Finset.mem_insert.mp hw with hw1 | hw1
      · subst hw1
        have hva : v ≠ w := hne
        rw [Function.update_self, Function.update_of_ne hva]
        intro hcon
        refine hk ?_
        rw [hF]
        exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv1, hadj.symm⟩, hcon⟩
      · have hva : v ≠ a := fun h => ha (h ▸ hv1)
        have hwa : w ≠ a := fun h => ha (h ▸ hw1)
        rw [Function.update_of_ne hva, Function.update_of_ne hwa]
        exact hc v hv1 w hw1 hadj
  obtain ⟨c, hc⟩ := key Finset.univ
  exact ⟨c, fun v w hadj => hc v (Finset.mem_univ v) w (Finset.mem_univ w) hadj⟩

/-! ### The Metropolis chain as a uniform proposal chain -/

variable (G : SimpleGraph Vv) [DecidableRel G.Adj] {q : ℕ}

/-- The Metropolis update: recolour `v` with `k`, keeping the result only if it is
again a proper colouring. -/
private def upd (x : {c : Vv → Fin q // IsProperColoring G c}) (v : Vv) (k : Fin q) :
    {c : Vv → Fin q // IsProperColoring G c} :=
  if h : IsProperColoring G (Function.update x.1 v k) then ⟨_, h⟩ else x

/-- The number of proposals `(v,k)` that turn `x` into `x'`. -/
private def cnt (x x' : {c : Vv → Fin q // IsProperColoring G c}) : ℕ :=
  (Finset.univ.filter fun p : Vv × Fin q => upd G x p.1 p.2 = x').card

private lemma upd_val_of_ne {x x' : {c : Vv → Fin q // IsProperColoring G c}}
    {v : Vv} {k : Fin q} (h : upd G x v k = x') (hne : x' ≠ x) :
    x'.1 = Function.update x.1 v k := by
  simp only [upd] at h
  split_ifs at h with hp
  · rw [← h]
  · exact absurd h (Ne.symm hne)

private lemma diff_subset_of_upd {x x' : {c : Vv → Fin q // IsProperColoring G c}}
    {v : Vv} {k : Fin q} (h : x'.1 = Function.update x.1 v k) :
    diffSet x.1 x'.1 ⊆ {v} := by
  intro w hw
  rw [mem_diffSet] at hw
  by_contra hcon
  refine hw ?_
  rw [h, Function.update_of_ne (by simpa using hcon)]

private lemma cnt_off_diag (x x' : {c : Vv → Fin q // IsProperColoring G c})
    (hne : x' ≠ x) :
    (cnt G x x' : ℝ) = if (diffSet x.1 x'.1).card = 1 then 1 else 0 := by
  classical
  by_cases hc : (diffSet x.1 x'.1).card = 1
  · rw [if_pos hc]
    obtain ⟨v₀, hv₀⟩ := Finset.card_eq_one.mp hc
    have hx' : x'.1 = Function.update x.1 v₀ (x'.1 v₀) := by
      funext w
      by_cases hw : w = v₀
      · rw [hw, Function.update_self]
      · rw [Function.update_of_ne hw]
        by_contra hcon
        have : w ∈ diffSet x.1 x'.1 := (mem_diffSet _ _ _).mpr (Ne.symm hcon)
        rw [hv₀, Finset.mem_singleton] at this
        exact hw this
    have hmem : upd G x v₀ (x'.1 v₀) = x' := by
      simp only [upd]
      rw [dif_pos (by rw [← hx']; exact x'.2)]
      exact Subtype.ext hx'.symm
    have hsingle : (Finset.univ.filter fun p : Vv × Fin q => upd G x p.1 p.2 = x')
        = {(v₀, x'.1 v₀)} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨by simpa using hmem, ?_⟩
      rintro ⟨v, k⟩ hp
      simp only [Finset.mem_filter] at hp
      have hval := upd_val_of_ne G hp.2 hne
      have hsub := diff_subset_of_upd G hval
      rw [hv₀] at hsub
      have hvv : v₀ = v := by
        have : v₀ ∈ ({v} : Finset Vv) := hsub (Finset.mem_singleton_self v₀)
        simpa using this
      subst hvv
      have hk : k = x'.1 v₀ := by rw [hval, Function.update_self]
      simp [hk]
    simp only [cnt, hsingle]
    simp
  · rw [if_neg hc]
    have : (Finset.univ.filter fun p : Vv × Fin q => upd G x p.1 p.2 = x') = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr ?_
      rintro ⟨v, k⟩ - hp
      have hval := upd_val_of_ne G hp hne
      have hsub := diff_subset_of_upd G hval
      have : (diffSet x.1 x'.1).card ≤ 1 := by
        simpa using Finset.card_le_card hsub
      have hc0 : (diffSet x.1 x'.1).card = 0 := by omega
      have : x'.1 = x.1 := by
        funext w
        by_contra hcon
        have : w ∈ diffSet x.1 x'.1 := (mem_diffSet _ _ _).mpr (Ne.symm hcon)
        rw [Finset.card_eq_zero.mp hc0] at this
        simpa using this
      exact hne (Subtype.ext this)
    simp only [cnt, this]
    simp

private lemma sum_cnt (x : {c : Vv → Fin q // IsProperColoring G c}) :
    ∑ x' : {c : Vv → Fin q // IsProperColoring G c}, cnt G x x'
      = Fintype.card Vv * q := by
  classical
  have := Finset.card_eq_sum_card_fiberwise
    (f := fun p : Vv × Fin q => upd G x p.1 p.2)
    (s := (Finset.univ : Finset (Vv × Fin q)))
    (t := (Finset.univ : Finset {c : Vv → Fin q // IsProperColoring G c}))
    (fun p _ => Finset.mem_univ _)
  simp only [cnt]
  rw [← this]
  simp [Fintype.card_prod]

private lemma sum_div_const {α : Type*} (s : Finset α) (f : α → ℝ) (c : ℝ) :
    (∑ i ∈ s, f i) / c = ∑ i ∈ s, f i / c := by
  simp [div_eq_mul_inv, Finset.sum_mul]

private lemma metro_eq_cnt (hq0 : 0 < q) (hN : 0 < Fintype.card Vv)
    (x x' : {c : Vv → Fin q // IsProperColoring G c}) :
    coloringMetropolis G q x x' = (cnt G x x' : ℝ) / ((Fintype.card Vv : ℝ) * q) := by
  classical
  have hpos : (0 : ℝ) < (Fintype.card Vv : ℝ) * q := by
    have h1 : (0 : ℝ) < (Fintype.card Vv : ℝ) := by exact_mod_cast hN
    have h2 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
    positivity
  have hstep : ∀ z : {c : Vv → Fin q // IsProperColoring G c}, z ≠ x →
      coloringStep G q x z = (cnt G x z : ℝ) / ((Fintype.card Vv : ℝ) * q) := by
    intro z hz
    simp only [coloringStep]
    rw [cnt_off_diag G x z hz]
    have hfilt : (Finset.univ.filter fun v : Vv => x.1 v ≠ z.1 v) = diffSet x.1 z.1 := rfl
    rw [hfilt]
    split_ifs
    · rw [one_div]
    · simp
  by_cases hx : x' = x
  · subst hx
    simp only [coloringMetropolis, if_true]
    have hsplit : ∑ z ∈ ({x'}ᶜ : Finset {c : Vv → Fin q // IsProperColoring G c}),
        coloringStep G q x' z
          = ∑ z ∈ ({x'}ᶜ : Finset {c : Vv → Fin q // IsProperColoring G c}),
            (cnt G x' z : ℝ) / ((Fintype.card Vv : ℝ) * q) := by
      refine Finset.sum_congr rfl fun z hz => hstep z ?_
      simpa using hz
    rw [hsplit, ← sum_div_const]
    have h1 : ∑ z : {c : Vv → Fin q // IsProperColoring G c}, (cnt G x' z : ℝ)
        = (Fintype.card Vv : ℝ) * q := by
      rw [← Nat.cast_sum, sum_cnt G x']
      push_cast
      ring
    have h2 := Finset.sum_add_sum_compl
      ({x'} : Finset {c : Vv → Fin q // IsProperColoring G c})
      (fun z => (cnt G x' z : ℝ))
    rw [Finset.sum_singleton, h1] at h2
    have htot : ∑ z ∈ ({x'}ᶜ : Finset {c : Vv → Fin q // IsProperColoring G c}),
        (cnt G x' z : ℝ) = (Fintype.card Vv : ℝ) * q - (cnt G x' x' : ℝ) := by linarith
    rw [htot]
    field_simp
    ring
  · simp only [coloringMetropolis]
    rw [if_neg hx]
    exact hstep x' hx

private lemma metro_stochastic (hq0 : 0 < q) (hN : 0 < Fintype.card Vv) :
    IsStochastic (coloringMetropolis G q) := by
  have hpos : (0 : ℝ) < (Fintype.card Vv : ℝ) * q := by
    have h1 : (0 : ℝ) < (Fintype.card Vv : ℝ) := by exact_mod_cast hN
    have h2 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
    positivity
  refine ⟨fun x x' => ?_, fun x => ?_⟩
  · rw [metro_eq_cnt G hq0 hN]
    positivity
  · rw [Finset.sum_congr rfl fun x' _ => metro_eq_cnt G hq0 hN x x', ← sum_div_const,
      ← Nat.cast_sum, sum_cnt G x]
    push_cast
    field_simp

private lemma metro_symm (x y : {c : Vv → Fin q // IsProperColoring G c}) :
    coloringMetropolis G q x y = coloringMetropolis G q y x := by
  have hstep : coloringStep G q x y = coloringStep G q y x := by
    have hfilt : (Finset.univ.filter fun v : Vv => x.1 v ≠ y.1 v)
        = (Finset.univ.filter fun v : Vv => y.1 v ≠ x.1 v) :=
      Finset.filter_congr fun v _ => ⟨fun h => Ne.symm h, fun h => Ne.symm h⟩
    simp only [coloringStep, hfilt]
  by_cases hxy : y = x
  · rw [hxy]
  · simp only [coloringMetropolis, if_neg hxy, if_neg (Ne.symm hxy)]
    exact hstep

private lemma metro_stationary (hq0 : 0 < q) (hN : 0 < Fintype.card Vv)
    (hne : Nonempty {c : Vv → Fin q // IsProperColoring G c}) :
    IsStationary (coloringMetropolis G q)
      (uniformDist {c : Vv → Fin q // IsProperColoring G c}) := by
  have hcard : (0 : ℝ) < (Fintype.card {c : Vv → Fin q // IsProperColoring G c} : ℝ) := by
    have := Fintype.card_pos (α := {c : Vv → Fin q // IsProperColoring G c})
    exact_mod_cast this
  have hrow := (metro_stochastic G hq0 hN).2
  refine ⟨⟨fun z => by simp only [uniformDist]; positivity, ?_⟩, ?_⟩
  · simp only [uniformDist, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  · funext y
    simp only [Matrix.vecMul, dotProduct, uniformDist]
    rw [← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun x _ => metro_symm G x y]
    rw [hrow y]
    ring

/-! ### The identity coupling: same vertex, same colour -/

/-- Couple two copies of the chain by feeding them the same proposal `(v,k)`. -/
private def Qc (_a _b : {c : Vv → Fin q // IsProperColoring G c}) :
    Matrix ({c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c}) ({c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c}) ℝ :=
  fun p p' => ((Finset.univ.filter fun w : Vv × Fin q =>
      upd G p.1 w.1 w.2 = p'.1 ∧ upd G p.2 w.1 w.2 = p'.2).card : ℝ)
    / ((Fintype.card Vv : ℝ) * q)

private lemma Qc_apply (a b : {c : Vv → Fin q // IsProperColoring G c}) (p p' : {c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c}) :
    Qc G a b p p' = ((Finset.univ.filter fun w : Vv × Fin q =>
      (fun w : Vv × Fin q => (upd G p.1 w.1 w.2, upd G p.2 w.1 w.2)) w = p').card : ℝ)
      / ((Fintype.card Vv : ℝ) * q) := by
  simp only [Qc, Prod.ext_iff]

/-- Pushing a function forward along the proposal map. -/
private lemma push_sum (p : {c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c}) (g : {c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c} → ℝ) :
    ∑ p' : {c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c},
        ((Finset.univ.filter fun w : Vv × Fin q =>
          (upd G p.1 w.1 w.2, upd G p.2 w.1 w.2) = p').card : ℝ) * g p'
      = ∑ w : Vv × Fin q, g (upd G p.1 w.1 w.2, upd G p.2 w.1 w.2) := by
  classical
  have := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Vv × Fin q)))
    (t := (Finset.univ : Finset ({c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c})))
    (g := fun w : Vv × Fin q => (upd G p.1 w.1 w.2, upd G p.2 w.1 w.2))
    (f := fun w : Vv × Fin q => g (upd G p.1 w.1 w.2, upd G p.2 w.1 w.2))
    (fun w _ => Finset.mem_univ _)
  rw [← this]
  refine Finset.sum_congr rfl fun p' _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => g p') ?_, Finset.sum_const, nsmul_eq_mul]
  intro w hw
  simp only [Finset.mem_filter] at hw
  rw [hw.2]

private lemma Qc_sum (a b : {c : Vv → Fin q // IsProperColoring G c}) (p : {c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c}) (g : {c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c} → ℝ) :
    ∑ p' : {c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c}, Qc G a b p p' * g p'
      = (∑ w : Vv × Fin q, g (upd G p.1 w.1 w.2, upd G p.2 w.1 w.2))
        / ((Fintype.card Vv : ℝ) * q) := by
  classical
  calc ∑ p' : {c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c}, Qc G a b p p' * g p'
      = ∑ p' : {c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c},
          (((Finset.univ.filter fun w : Vv × Fin q =>
            (upd G p.1 w.1 w.2, upd G p.2 w.1 w.2) = p').card : ℝ) * g p')
              / ((Fintype.card Vv : ℝ) * q) := by
        refine Finset.sum_congr rfl fun p' _ => ?_
        rw [Qc_apply G a b p p', div_mul_eq_mul_div]
    _ = (∑ p' : {c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c},
          (((Finset.univ.filter fun w : Vv × Fin q =>
            (upd G p.1 w.1 w.2, upd G p.2 w.1 w.2) = p').card : ℝ) * g p'))
              / ((Fintype.card Vv : ℝ) * q) := (sum_div_const _ _ _).symm
    _ = (∑ w : Vv × Fin q, g (upd G p.1 w.1 w.2, upd G p.2 w.1 w.2))
          / ((Fintype.card Vv : ℝ) * q) := by rw [push_sum]

private lemma upd_diag (x : {c : Vv → Fin q // IsProperColoring G c}) (w : Vv × Fin q) :
    (upd G x w.1 w.2, upd G x w.1 w.2) ∈ pairDiagonal {c : Vv → Fin q // IsProperColoring G c} := by
  simp [pairDiagonal]

private lemma Qc_markovian (hq0 : 0 < q) (hN : 0 < Fintype.card Vv) (a b : {c : Vv → Fin q // IsProperColoring G c}) :
    IsMarkovianCoupling (coloringMetropolis G q) (Qc G a b) := by
  classical
  have hpos : (0 : ℝ) < (Fintype.card Vv : ℝ) * q := by
    have h1 : (0 : ℝ) < (Fintype.card Vv : ℝ) := by exact_mod_cast hN
    have h2 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
    positivity
  have hcardVq : ((Fintype.card (Vv × Fin q) : ℕ) : ℝ) = (Fintype.card Vv : ℝ) * q := by
    simp [Fintype.card_prod]
  refine ⟨⟨fun p p' => by rw [Qc]; positivity, fun p => ?_⟩, ?_, ?_, ?_⟩
  · have := Qc_sum G a b p (fun _ => (1 : ℝ))
    simp only [mul_one] at this
    rw [this]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcardVq]
    field_simp
  · -- first marginal
    intro p x'
    have hfib : ∑ y' : {c : Vv → Fin q // IsProperColoring G c},
        ((Finset.univ.filter fun w : Vv × Fin q =>
          upd G p.1 w.1 w.2 = x' ∧ upd G p.2 w.1 w.2 = y').card : ℝ)
        = (cnt G p.1 x' : ℝ) := by
      have hh := Finset.card_eq_sum_card_fiberwise
        (f := fun w : Vv × Fin q => upd G p.2 w.1 w.2)
        (s := (Finset.univ.filter fun w : Vv × Fin q => upd G p.1 w.1 w.2 = x'))
        (t := (Finset.univ : Finset {c : Vv → Fin q // IsProperColoring G c})) (fun w _ => Finset.mem_univ _)
      simp only [cnt]
      rw [hh, Nat.cast_sum]
      refine Finset.sum_congr rfl fun y' _ => ?_
      congr 2
      rw [Finset.filter_filter]
    simp only [Qc]
    rw [← sum_div_const, hfib, ← metro_eq_cnt G hq0 hN]
  · -- second marginal
    intro p y'
    have hfib : ∑ x' : {c : Vv → Fin q // IsProperColoring G c},
        ((Finset.univ.filter fun w : Vv × Fin q =>
          upd G p.1 w.1 w.2 = x' ∧ upd G p.2 w.1 w.2 = y').card : ℝ)
        = (cnt G p.2 y' : ℝ) := by
      have hh := Finset.card_eq_sum_card_fiberwise
        (f := fun w : Vv × Fin q => upd G p.1 w.1 w.2)
        (s := (Finset.univ.filter fun w : Vv × Fin q => upd G p.2 w.1 w.2 = y'))
        (t := (Finset.univ : Finset {c : Vv → Fin q // IsProperColoring G c})) (fun w _ => Finset.mem_univ _)
      simp only [cnt]
      rw [hh, Nat.cast_sum]
      refine Finset.sum_congr rfl fun x' _ => ?_
      congr 2
      rw [Finset.filter_filter]
      exact Finset.filter_congr fun w _ => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    simp only [Qc]
    rw [← sum_div_const, hfib, ← metro_eq_cnt G hq0 hN]
  · -- the coupling stays together
    intro x r hr
    simp only [Qc]
    have : (Finset.univ.filter fun w : Vv × Fin q =>
        upd G x w.1 w.2 = r.1 ∧ upd G x w.1 w.2 = r.2) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun w _ h => hr ?_
      rw [← h.1, ← h.2]
    rw [this]
    simp

/-! ### One-step contraction of the Hamming distance -/

/-- The Metropolis proposal at `v` is accepted exactly when no neighbour of `v`
already carries the colour `k`. -/
private lemma acc_iff (x : {c : Vv → Fin q // IsProperColoring G c}) (v : Vv) (k : Fin q) :
    IsProperColoring G (Function.update x.1 v k) ↔ ∀ w : Vv, G.Adj v w → k ≠ x.1 w := by
  constructor
  · intro h w hvw
    have := h v w hvw
    rwa [Function.update_self, Function.update_of_ne (Ne.symm hvw.ne)] at this
  · intro h p r hpr
    by_cases hp : p = v
    · subst hp
      rw [Function.update_self, Function.update_of_ne (Ne.symm hpr.ne)]
      exact h r hpr
    · by_cases hr : r = v
      · subst hr
        rw [Function.update_self, Function.update_of_ne hp]
        exact fun hcon => h p hpr.symm hcon.symm
      · rw [Function.update_of_ne hp, Function.update_of_ne hr]
        exact x.2 p r hpr

private lemma upd_off (x : {c : Vv → Fin q // IsProperColoring G c}) (v : Vv) (k : Fin q) (w : Vv) (hw : w ≠ v) :
    (upd G x v k).1 w = x.1 w := by
  simp only [upd]
  split_ifs with h
  · exact Function.update_of_ne hw _ _
  · rfl

private lemma upd_at_acc {x : {c : Vv → Fin q // IsProperColoring G c}} {v : Vv} {k : Fin q}
    (h : IsProperColoring G (Function.update x.1 v k)) : (upd G x v k).1 v = k := by
  simp only [upd, dif_pos h]
  exact Function.update_self _ _ _

private lemma upd_at_rej {x : {c : Vv → Fin q // IsProperColoring G c}} {v : Vv} {k : Fin q}
    (h : ¬ IsProperColoring G (Function.update x.1 v k)) : (upd G x v k).1 v = x.1 v := by
  simp only [upd, dif_neg h]

/-- Off the updated vertex the disagreement set is unchanged. -/
private lemma diff_upd_sub (a b : {c : Vv → Fin q // IsProperColoring G c}) (v : Vv) (k : Fin q) :
    diffSet (upd G a v k).1 (upd G b v k).1 ⊆ insert v ((diffSet a.1 b.1).erase v) := by
  intro w hw
  rw [mem_diffSet] at hw
  by_cases hwv : w = v
  · rw [hwv]; exact Finset.mem_insert_self _ _
  · refine Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwv, ?_⟩)
    rw [mem_diffSet]
    rwa [upd_off G a v k w hwv, upd_off G b v k w hwv] at hw

private lemma diff_upd_sub' (a b : {c : Vv → Fin q // IsProperColoring G c}) (v : Vv) (k : Fin q)
    (hv : v ∉ diffSet (upd G a v k).1 (upd G b v k).1) :
    diffSet (upd G a v k).1 (upd G b v k).1 ⊆ (diffSet a.1 b.1).erase v := by
  intro w hw
  rcases Finset.mem_insert.mp (diff_upd_sub G a b v k hw) with h | h
  · exact absurd (h ▸ hw) hv
  · exact h

/-- Proposals rejected by at least one of the two chains. -/
private def badSet (a b : {c : Vv → Fin q // IsProperColoring G c}) (v : Vv) : Finset (Fin q) :=
  Finset.univ.filter fun k => ¬(IsProperColoring G (Function.update a.1 v k)
    ∧ IsProperColoring G (Function.update b.1 v k))

/-- Proposals accepted by exactly one of the two chains. -/
private def oneSet (a b : {c : Vv → Fin q // IsProperColoring G c}) (v : Vv) : Finset (Fin q) :=
  Finset.univ.filter fun k =>
    (IsProperColoring G (Function.update a.1 v k) ∧
      ¬IsProperColoring G (Function.update b.1 v k)) ∨
    (¬IsProperColoring G (Function.update a.1 v k) ∧
      IsProperColoring G (Function.update b.1 v k))

private lemma not_acc (x : {c : Vv → Fin q // IsProperColoring G c}) (v : Vv) (k : Fin q)
    (h : ¬IsProperColoring G (Function.update x.1 v k)) :
    ∃ w : Vv, G.Adj v w ∧ k = x.1 w := by
  by_contra hcon
  refine h ((acc_iff G x v k).mpr fun w hvw hk => hcon ⟨w, hvw, hk⟩)

private lemma badSet_card_le (a b : {c : Vv → Fin q // IsProperColoring G c}) (v : Vv) :
    (badSet G a b v).card
      ≤ G.maxDegree + (G.neighborFinset v ∩ diffSet a.1 b.1).card := by
  classical
  have hsub : badSet G a b v
      ⊆ (G.neighborFinset v).image a.1
        ∪ (G.neighborFinset v ∩ diffSet a.1 b.1).image b.1 := by
    intro k hk
    simp only [badSet, Finset.mem_filter, not_and] at hk
    by_cases hA : IsProperColoring G (Function.update a.1 v k)
    · obtain ⟨w, hvw, hkw⟩ := not_acc G b v k (hk.2 hA)
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, ?_, hkw.symm⟩)
      refine Finset.mem_inter.mpr ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr hvw, ?_⟩
      rw [mem_diffSet]
      have := (acc_iff G a v k).mp hA w hvw
      rw [hkw] at this
      exact fun hcon => this hcon.symm
    · obtain ⟨w, hvw, hkw⟩ := not_acc G a v k hA
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨w, (SimpleGraph.mem_neighborFinset _ _ _).mpr hvw, hkw.symm⟩)
  calc (badSet G a b v).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ((G.neighborFinset v).image a.1).card
        + ((G.neighborFinset v ∩ diffSet a.1 b.1).image b.1).card := Finset.card_union_le _ _
    _ ≤ (G.neighborFinset v).card + (G.neighborFinset v ∩ diffSet a.1 b.1).card := by
        exact Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ ≤ G.maxDegree + (G.neighborFinset v ∩ diffSet a.1 b.1).card := by
        have : (G.neighborFinset v).card = G.degree v := rfl
        have h2 := G.degree_le_maxDegree v
        omega

private lemma oneSet_card_le (a b : {c : Vv → Fin q // IsProperColoring G c}) (v : Vv) :
    (oneSet G a b v).card ≤ 2 * (G.neighborFinset v ∩ diffSet a.1 b.1).card := by
  classical
  have hsub : oneSet G a b v
      ⊆ (G.neighborFinset v ∩ diffSet a.1 b.1).image b.1
        ∪ (G.neighborFinset v ∩ diffSet a.1 b.1).image a.1 := by
    intro k hk
    simp only [oneSet, Finset.mem_filter] at hk
    rcases hk.2 with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · obtain ⟨w, hvw, hkw⟩ := not_acc G b v k hB
      refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨w, ?_, hkw.symm⟩)
      refine Finset.mem_inter.mpr ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr hvw, ?_⟩
      rw [mem_diffSet]
      have := (acc_iff G a v k).mp hA w hvw
      rw [hkw] at this
      exact fun hcon => this hcon.symm
    · obtain ⟨w, hvw, hkw⟩ := not_acc G a v k hA
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, ?_, hkw.symm⟩)
      refine Finset.mem_inter.mpr ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr hvw, ?_⟩
      rw [mem_diffSet]
      have := (acc_iff G b v k).mp hB w hvw
      rw [hkw] at this
      exact this
  calc (oneSet G a b v).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ((G.neighborFinset v ∩ diffSet a.1 b.1).image b.1).card
        + ((G.neighborFinset v ∩ diffSet a.1 b.1).image a.1).card := Finset.card_union_le _ _
    _ ≤ 2 * (G.neighborFinset v ∩ diffSet a.1 b.1).card := by
        have h1 : ((G.neighborFinset v ∩ diffSet a.1 b.1).image b.1).card
            ≤ (G.neighborFinset v ∩ diffSet a.1 b.1).card := Finset.card_image_le
        have h2 : ((G.neighborFinset v ∩ diffSet a.1 b.1).image a.1).card
            ≤ (G.neighborFinset v ∩ diffSet a.1 b.1).card := Finset.card_image_le
        omega

private lemma sum_local_diff (A : Finset Vv) :
    ∑ v : Vv, (G.neighborFinset v ∩ A).card ≤ G.maxDegree * A.card := by
  classical
  have hstep : ∀ v : Vv, (G.neighborFinset v ∩ A).card
      = ∑ w ∈ A, if w ∈ G.neighborFinset v then 1 else 0 := by
    intro v
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
  rw [Finset.sum_congr rfl fun v _ => hstep v, Finset.sum_comm]
  have hswap : ∀ w : Vv, ∑ v : Vv, (if w ∈ G.neighborFinset v then 1 else 0)
      = G.degree w := by
    intro w
    rw [← Finset.card_filter]
    have : (Finset.univ.filter fun v : Vv => w ∈ G.neighborFinset v)
        = G.neighborFinset w := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborFinset]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    rw [this]
    rfl
  rw [Finset.sum_congr rfl fun w _ => hswap w]
  calc ∑ w ∈ A, G.degree w ≤ ∑ _w ∈ A, G.maxDegree :=
        Finset.sum_le_sum fun w _ => G.degree_le_maxDegree w
    _ = G.maxDegree * A.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- The proposals that leave the two chains disagreeing at the updated vertex. -/
private def excSet (a b : {c : Vv → Fin q // IsProperColoring G c}) (v : Vv) : Finset (Fin q) :=
  Finset.univ.filter fun k => v ∈ diffSet (upd G a v k).1 (upd G b v k).1

private lemma exc_sub_bad (a b : {c : Vv → Fin q // IsProperColoring G c}) (v : Vv) : excSet G a b v ⊆ badSet G a b v := by
  intro k hk
  simp only [excSet, Finset.mem_filter, mem_diffSet] at hk
  simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨hA, hB⟩
  exact hk.2 (by rw [upd_at_acc G hA, upd_at_acc G hB])

private lemma exc_sub_one (a b : {c : Vv → Fin q // IsProperColoring G c}) (v : Vv) (hv : v ∉ diffSet a.1 b.1) :
    excSet G a b v ⊆ oneSet G a b v := by
  intro k hk
  simp only [excSet, Finset.mem_filter, mem_diffSet] at hk
  rw [mem_diffSet] at hv
  simp only [not_not] at hv
  simp only [oneSet, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hA : IsProperColoring G (Function.update a.1 v k)
  · by_cases hB : IsProperColoring G (Function.update b.1 v k)
    · exact absurd (by rw [upd_at_acc G hA, upd_at_acc G hB]) hk.2
    · exact Or.inl ⟨hA, hB⟩
  · by_cases hB : IsProperColoring G (Function.update b.1 v k)
    · exact Or.inr ⟨hA, hB⟩
    · exact absurd (by rw [upd_at_rej G hA, upd_at_rej G hB, hv]) hk.2

private lemma per_vertex (a b : {c : Vv → Fin q // IsProperColoring G c}) (v : Vv) :
    ∑ k : Fin q, ((diffSet (upd G a v k).1 (upd G b v k).1).card : ℝ)
      ≤ (q : ℝ) * (((diffSet a.1 b.1).erase v).card : ℝ)
        + ((excSet G a b v).card : ℝ) := by
  classical
  have hterm : ∀ k : Fin q, ((diffSet (upd G a v k).1 (upd G b v k).1).card : ℝ)
      ≤ (((diffSet a.1 b.1).erase v).card : ℝ)
        + (if k ∈ excSet G a b v then (1 : ℝ) else 0) := by
    intro k
    by_cases hk : k ∈ excSet G a b v
    · rw [if_pos hk]
      have := Finset.card_le_card (diff_upd_sub G a b v k)
      have h2 := Finset.card_insert_le v ((diffSet a.1 b.1).erase v)
      have : (diffSet (upd G a v k).1 (upd G b v k).1).card
          ≤ ((diffSet a.1 b.1).erase v).card + 1 := le_trans this h2
      exact_mod_cast this
    · rw [if_neg hk, add_zero]
      have hv : v ∉ diffSet (upd G a v k).1 (upd G b v k).1 := by
        simpa [excSet] using hk
      exact_mod_cast Finset.card_le_card (diff_upd_sub' G a b v k hv)
  calc ∑ k : Fin q, ((diffSet (upd G a v k).1 (upd G b v k).1).card : ℝ)
      ≤ ∑ k : Fin q, ((((diffSet a.1 b.1).erase v).card : ℝ)
          + (if k ∈ excSet G a b v then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = (q : ℝ) * (((diffSet a.1 b.1).erase v).card : ℝ)
          + ((excSet G a b v).card : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        congr 1
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

private lemma erase_card_eq (A : Finset Vv) (v : Vv) :
    ((A.erase v).card : ℝ) = (A.card : ℝ) - (if v ∈ A then (1 : ℝ) else 0) := by
  by_cases hv : v ∈ A
  · rw [if_pos hv]
    have := Finset.card_erase_add_one hv
    have : ((A.erase v).card : ℝ) + 1 = (A.card : ℝ) := by exact_mod_cast this
    linarith
  · rw [if_neg hv, Finset.erase_eq_of_notMem hv]
    ring

private lemma exc_total (a b : {c : Vv → Fin q // IsProperColoring G c}) :
    ∑ v : Vv, ((excSet G a b v).card : ℝ)
      ≤ 3 * (G.maxDegree : ℝ) * ((diffSet a.1 b.1).card : ℝ) := by
  classical
  set A : Finset Vv := diffSet a.1 b.1 with hA
  set m : Vv → ℝ := fun v => ((G.neighborFinset v ∩ A).card : ℝ) with hm
  have hmnn : ∀ v, 0 ≤ m v := fun v => by rw [hm]; positivity
  have hmtot : ∑ v : Vv, m v ≤ (G.maxDegree : ℝ) * (A.card : ℝ) := by
    have := sum_local_diff G A
    have hc : ((∑ v : Vv, (G.neighborFinset v ∩ A).card : ℕ) : ℝ)
        ≤ ((G.maxDegree * A.card : ℕ) : ℝ) := by exact_mod_cast this
    rw [Nat.cast_sum] at hc
    push_cast at hc
    exact hc
  have hsplit := Finset.sum_add_sum_compl A (fun v => ((excSet G a b v).card : ℝ))
  have hin : ∑ v ∈ A, ((excSet G a b v).card : ℝ)
      ≤ (G.maxDegree : ℝ) * (A.card : ℝ) + ∑ v ∈ A, m v := by
    have h1 : ∀ v ∈ A, ((excSet G a b v).card : ℝ)
        ≤ (G.maxDegree : ℝ) + m v := by
      intro v _
      have h2 := le_trans (Finset.card_le_card (exc_sub_bad G a b v)) (badSet_card_le G a b v)
      have : ((excSet G a b v).card : ℝ) ≤ ((G.maxDegree + (G.neighborFinset v ∩ A).card : ℕ) : ℝ) :=
        by exact_mod_cast h2
      rw [hm]
      push_cast at this ⊢
      exact this
    calc ∑ v ∈ A, ((excSet G a b v).card : ℝ) ≤ ∑ v ∈ A, ((G.maxDegree : ℝ) + m v) :=
          Finset.sum_le_sum h1
      _ = (G.maxDegree : ℝ) * (A.card : ℝ) + ∑ v ∈ A, m v := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hout : ∑ v ∈ Aᶜ, ((excSet G a b v).card : ℝ) ≤ ∑ v ∈ Aᶜ, 2 * m v := by
    refine Finset.sum_le_sum fun v hv => ?_
    have hvA : v ∉ A := by simpa using hv
    have h2 := le_trans (Finset.card_le_card (exc_sub_one G a b v hvA)) (oneSet_card_le G a b v)
    have : ((excSet G a b v).card : ℝ) ≤ ((2 * (G.neighborFinset v ∩ A).card : ℕ) : ℝ) :=
      by exact_mod_cast h2
    rw [hm]
    push_cast at this ⊢
    exact this
  have hmin : 0 ≤ ∑ v ∈ A, m v := Finset.sum_nonneg fun v _ => hmnn v
  have hmout : 0 ≤ ∑ v ∈ Aᶜ, m v := Finset.sum_nonneg fun v _ => hmnn v
  have hmsplit := Finset.sum_add_sum_compl A m
  have hbound : ∑ v ∈ A, m v + ∑ v ∈ Aᶜ, 2 * m v
      ≤ 2 * ((G.maxDegree : ℝ) * (A.card : ℝ)) := by
    rw [← Finset.mul_sum]
    nlinarith [hmtot, hmsplit, hmin, hmout]
  calc ∑ v : Vv, ((excSet G a b v).card : ℝ)
      = ∑ v ∈ A, ((excSet G a b v).card : ℝ) + ∑ v ∈ Aᶜ, ((excSet G a b v).card : ℝ) :=
        hsplit.symm
    _ ≤ ((G.maxDegree : ℝ) * (A.card : ℝ) + ∑ v ∈ A, m v) + ∑ v ∈ Aᶜ, 2 * m v :=
        add_le_add hin hout
    _ ≤ 3 * (G.maxDegree : ℝ) * (A.card : ℝ) := by linarith

private lemma contraction_count (a b : {c : Vv → Fin q // IsProperColoring G c}) :
    ∑ w : Vv × Fin q, ((diffSet (upd G a w.1 w.2).1 (upd G b w.1 w.2).1).card : ℝ)
      ≤ ((Fintype.card Vv : ℝ) * q - q + 3 * G.maxDegree)
        * ((diffSet a.1 b.1).card : ℝ) := by
  classical
  set A : Finset Vv := diffSet a.1 b.1 with hA
  have herase : ∑ v : Vv, ((A.erase v).card : ℝ)
      = (Fintype.card Vv : ℝ) * (A.card : ℝ) - (A.card : ℝ) := by
    rw [Finset.sum_congr rfl fun v _ => erase_card_eq A v, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  calc ∑ w : Vv × Fin q, ((diffSet (upd G a w.1 w.2).1 (upd G b w.1 w.2).1).card : ℝ)
      = ∑ v : Vv, ∑ k : Fin q,
          ((diffSet (upd G a v k).1 (upd G b v k).1).card : ℝ) := by
        rw [Fintype.sum_prod_type]
    _ ≤ ∑ v : Vv, ((q : ℝ) * ((A.erase v).card : ℝ) + ((excSet G a b v).card : ℝ)) :=
        Finset.sum_le_sum fun v _ => per_vertex G a b v
    _ = (q : ℝ) * (∑ v : Vv, ((A.erase v).card : ℝ))
          + ∑ v : Vv, ((excSet G a b v).card : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (q : ℝ) * ((Fintype.card Vv : ℝ) * (A.card : ℝ) - (A.card : ℝ))
          + 3 * (G.maxDegree : ℝ) * (A.card : ℝ) := by
        rw [herase]
        have := exc_total G a b
        rw [← hA] at this
        linarith
    _ = ((Fintype.card Vv : ℝ) * q - q + 3 * G.maxDegree) * (A.card : ℝ) := by ring

/-! ### Chapman-Kolmogorov for path sums -/

section Paths

variable {W : Type*} [Fintype W] [DecidableEq W]

private lemma snoc_sum {t : ℕ} (f : (Fin (t + 2) → W) → ℝ) :
    ∑ ω : Fin (t + 2) → W, f ω
      = ∑ ω : Fin (t + 1) → W, ∑ y : W, f (Fin.snoc ω y) := by
  let e : ((Fin (t + 1) → W) × W) ≃ (Fin (t + 2) → W) :=
    { toFun := fun p => Fin.snoc p.1 p.2
      invFun := fun ω => (Fin.init ω, ω (Fin.last _))
      left_inv := by intro p; ext <;> simp
      right_inv := by intro ω; simp }
  have := Equiv.sum_comp e f
  rw [← this, Fintype.sum_prod_type]
  rfl

private lemma pathWeight_snoc (Q : Matrix W W ℝ) {t : ℕ}
    (ω : Fin (t + 1) → W) (y : W) :
    pathWeight Q (Fin.snoc ω y : Fin (t + 2) → W)
      = pathWeight Q ω * Q (ω (Fin.last t)) y := by
  simp only [pathWeight]
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [show (i.castSucc : Fin (t + 1)).castSucc = (i.castSucc : Fin (t+1)).castSucc from rfl,
      Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
  · rw [Fin.snoc_castSucc]
    congr 1
    rw [show (Fin.last t).succ = Fin.last (t + 1) from rfl, Fin.snoc_last]

private lemma group_by_last {t : ℕ} (F : (Fin (t + 1) → W) → ℝ) :
    ∑ ω : Fin (t + 1) → W, F ω
      = ∑ z : W, ∑ ω : Fin (t + 1) → W, (if ω (Fin.last t) = z then F ω else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp

private lemma sum_ite_last (c : ℝ) (f : W → ℝ) (h : W) :
    ∑ y : W, c * f y * (if y = h then (1 : ℝ) else 0) = c * f h := by
  have hcong : ∀ y ∈ (Finset.univ : Finset W), c * f y * (if y = h then (1 : ℝ) else 0)
      = if y = h then c * f h else 0 := by
    intro y _
    by_cases hy : y = h
    · subst hy; simp
    · simp [hy]
  rw [Finset.sum_congr rfl hcong]
  simp

/-- The `t`-step transition probability as a sum over trajectories. -/
private lemma path_pow (Q : Matrix W W ℝ) (t : ℕ) (z p : W) :
    ∑ ω : Fin (t + 1) → W,
        (if ω 0 = z ∧ ω (Fin.last t) = p then pathWeight Q ω else 0)
      = (Q ^ t) z p := by
  induction t generalizing p with
  | zero =>
    rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) W)
        (fun ω : Fin 1 → W => if ω 0 = z ∧ ω (Fin.last 0) = p then pathWeight Q ω else 0)
        (fun v : W => if v = z then (if p = z then (1 : ℝ) else 0) else 0)]
    · simp only [pow_zero, Matrix.one_apply]
      rw [Finset.sum_ite_eq' Finset.univ z]
      by_cases h : p = z
      · simp [h]
      · simp [h, Ne.symm h]
    · intro ω
      simp only [pathWeight, Finset.univ_eq_empty, Finset.prod_empty,
        Equiv.funUnique_apply]
      show (if ω 0 = z ∧ ω 0 = p then (1 : ℝ) else 0)
          = if ω 0 = z then (if p = z then (1 : ℝ) else 0) else 0
      by_cases h1 : ω 0 = z
      · rw [if_pos h1]
        by_cases h2 : p = z
        · rw [if_pos h2, if_pos ⟨h1, by rw [h1, h2]⟩]
        · rw [if_neg h2, if_neg]
          rintro ⟨-, hcon⟩
          exact h2 (by rw [← hcon, h1])
      · rw [if_neg h1, if_neg]
        rintro ⟨hcon, -⟩
        exact h1 hcon
  | succ t ih =>
    rw [snoc_sum]
    have key : ∀ (ω : Fin (t + 1) → W) (y : W),
        (if (Fin.snoc ω y : Fin (t + 2) → W) 0 = z ∧
              (Fin.snoc ω y : Fin (t + 2) → W) (Fin.last (t + 1)) = p then
            pathWeight Q (Fin.snoc ω y : Fin (t + 2) → W) else 0)
          = (if ω 0 = z then (1 : ℝ) else 0) * pathWeight Q ω *
              Q (ω (Fin.last t)) y * (if y = p then (1 : ℝ) else 0) := by
      intro ω y
      have h0 : (Fin.snoc ω y : Fin (t + 2) → W) 0 = ω 0 := by
        have : (0 : Fin (t + 2)) = Fin.castSucc (0 : Fin (t + 1)) := rfl
        rw [this, Fin.snoc_castSucc]
      have hl : (Fin.snoc ω y : Fin (t + 2) → W) (Fin.last (t + 1)) = y := by simp
      rw [h0, hl, pathWeight_snoc]
      by_cases hx : ω 0 = z <;> by_cases hy : y = p <;> simp [hx, hy] <;> ring
    calc ∑ ω : Fin (t + 1) → W, ∑ y : W, _
        = ∑ ω : Fin (t + 1) → W, ∑ y : W,
            ((if ω 0 = z then (1 : ℝ) else 0) * pathWeight Q ω *
              Q (ω (Fin.last t)) y * (if y = p then (1 : ℝ) else 0)) :=
          Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun y _ => key ω y
      _ = ∑ ω : Fin (t + 1) → W,
            ((if ω 0 = z then (1 : ℝ) else 0) * pathWeight Q ω * Q (ω (Fin.last t)) p) :=
          Finset.sum_congr rfl fun ω _ => sum_ite_last _ _ p
      _ = ∑ z' : W, (Q ^ t) z z' * Q z' p := by
          rw [group_by_last (t := t)]
          refine Finset.sum_congr rfl fun z' _ => ?_
          rw [← ih z', Finset.sum_mul]
          refine Finset.sum_congr rfl fun ω _ => ?_
          by_cases hz : ω (Fin.last t) = z'
          · by_cases hx : ω 0 = z <;> simp [hz, hx] <;> ring
          · simp [hz]
      _ = (Q ^ (t + 1)) z p := by rw [pow_succ, Matrix.mul_apply]

private lemma pow_nonneg_of_stochastic {Q : Matrix W W ℝ} (hQ : IsStochastic Q) (t : ℕ)
    (z p : W) : 0 ≤ (Q ^ t) z p := by
  induction t generalizing p with
  | zero => rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ t ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z' _ => mul_nonneg (ih z') (hQ.1 _ _)

end Paths

/-! ### Iterating the contraction -/

private def rhoP (p : {c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c}) : ℝ := ((diffSet p.1.1 p.2.1).card : ℝ)

private lemma rhoP_nonneg (p : {c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c}) : 0 ≤ rhoP G p := by
  rw [rhoP]; positivity

private lemma rhoP_le (p : {c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c}) : rhoP G p ≤ (Fintype.card Vv : ℝ) := by
  rw [rhoP]
  have : (diffSet p.1.1 p.2.1).card ≤ Fintype.card Vv := by
    simpa using Finset.card_le_card (Finset.subset_univ (diffSet p.1.1 p.2.1))
  exact_mod_cast this

private lemma rhoP_off_diag (p : {c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c}) (h : p ∉ pairDiagonal {c : Vv → Fin q // IsProperColoring G c}) :
    1 ≤ rhoP G p := by
  simp only [pairDiagonal, Finset.mem_filter, Finset.mem_univ, true_and] at h
  have hne : p.1.1 ≠ p.2.1 := fun hc => h (Subtype.ext hc)
  obtain ⟨v, hv⟩ : ∃ v : Vv, p.1.1 v ≠ p.2.1 v := by
    by_contra hcon
    exact hne (funext fun v => not_not.mp (fun hh => hcon ⟨v, hh⟩))
  have : (1 : ℕ) ≤ (diffSet p.1.1 p.2.1).card :=
    Finset.card_pos.mpr ⟨v, (mem_diffSet _ _ _).mpr hv⟩
  rw [rhoP]
  exact_mod_cast this

private lemma Qc_contract (hq0 : 0 < q) (hN : 0 < Fintype.card Vv) (a b : {c : Vv → Fin q // IsProperColoring G c})
    (p : {c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c}) :
    ∑ p' : {c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c}, Qc G a b p p' * rhoP G p'
      ≤ (1 - (1 - 3 * (G.maxDegree : ℝ) / q) / (Fintype.card Vv : ℝ)) * rhoP G p := by
  have hq : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hNr : (0 : ℝ) < (Fintype.card Vv : ℝ) := by exact_mod_cast hN
  rw [Qc_sum G a b p (rhoP G)]
  have hcc := contraction_count G p.1 p.2
  have hrho : ∀ w : Vv × Fin q, rhoP G (upd G p.1 w.1 w.2, upd G p.2 w.1 w.2)
      = ((diffSet (upd G p.1 w.1 w.2).1 (upd G p.2 w.1 w.2).1).card : ℝ) := fun w => rfl
  rw [Finset.sum_congr rfl fun w _ => hrho w]
  rw [div_le_iff₀ (by positivity)]
  have hp : rhoP G p = ((diffSet p.1.1 p.2.1).card : ℝ) := rfl
  rw [hp]
  have hfac : (1 - (1 - 3 * (G.maxDegree : ℝ) / q) / (Fintype.card Vv : ℝ))
      * ((diffSet p.1.1 p.2.1).card : ℝ) * ((Fintype.card Vv : ℝ) * q)
      = ((Fintype.card Vv : ℝ) * q - q + 3 * G.maxDegree)
        * ((diffSet p.1.1 p.2.1).card : ℝ) := by
    field_simp
    ring
  rw [hfac]
  exact hcc

private lemma pow_contract {W : Type*} [Fintype W] [DecidableEq W]
    (Q : Matrix W W ℝ) (hQ : IsStochastic Q) (r : W → ℝ) (hr : ∀ w, 0 ≤ r w)
    (κ : ℝ) (hκ : 0 ≤ κ) (hstep : ∀ z, ∑ p', Q z p' * r p' ≤ κ * r z) (t : ℕ) (z : W) :
    ∑ p' : W, (Q ^ t) z p' * r p' ≤ κ ^ t * r z := by
  induction t generalizing z with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul, pow_zero, one_mul]
    rw [Finset.sum_ite_eq Finset.univ z r]
    simp
  | succ t ih =>
    have hstep2 : ∑ p' : W, (Q ^ (t + 1)) z p' * r p'
        = ∑ z' : W, (Q ^ t) z z' * ∑ p' : W, Q z' p' * r p' := by
      have h1 : ∀ p' : W, (Q ^ (t + 1)) z p' * r p'
          = ∑ z' : W, (Q ^ t) z z' * Q z' p' * r p' := by
        intro p'; rw [pow_succ, Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_congr rfl fun p' _ => h1 p', Finset.sum_comm]
      refine Finset.sum_congr rfl fun z' _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p' _ => by ring
    rw [hstep2]
    calc ∑ z' : W, (Q ^ t) z z' * ∑ p' : W, Q z' p' * r p'
        ≤ ∑ z' : W, (Q ^ t) z z' * (κ * r z') :=
          Finset.sum_le_sum fun z' _ =>
            mul_le_mul_of_nonneg_left (hstep z') (pow_nonneg_of_stochastic hQ t z z')
      _ = κ * ∑ z' : W, (Q ^ t) z z' * r z' := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun z' _ => by ring
      _ ≤ κ * (κ ^ t * r z) := mul_le_mul_of_nonneg_left (ih z) hκ
      _ = κ ^ (t + 1) * r z := by ring

private lemma tail_le {W : Type*} [Fintype W] [DecidableEq W]
    (Q : Matrix W W ℝ) (hQ : IsStochastic Q) (r : W → ℝ) (hr : ∀ w, 0 ≤ r w)
    (S : Finset W) (hS : ∀ w ∉ S, 1 ≤ r w) (z : W) (t : ℕ) :
    setAvoidTailProb Q z S t ≤ ∑ p' : W, (Q ^ t) z p' * r p' := by
  have hpw : ∀ ω : Fin (t + 1) → W, 0 ≤ pathWeight Q ω :=
    fun ω => Finset.prod_nonneg fun i _ => hQ.1 _ _
  have hle : setAvoidTailProb Q z S t
      ≤ ∑ ω : Fin (t + 1) → W,
          (if ω 0 = z then pathWeight Q ω * r (ω (Fin.last t)) else 0) := by
    simp only [setAvoidTailProb]
    refine Finset.sum_le_sum fun ω _ => ?_
    by_cases hc : ω 0 = z ∧ ∀ i : Fin (t + 1), ω i ∉ S
    · rw [if_pos hc, if_pos hc.1]
      have h1 : (1 : ℝ) ≤ r (ω (Fin.last t)) := hS _ (hc.2 _)
      nlinarith [hpw ω]
    · rw [if_neg hc]
      by_cases hz : ω 0 = z
      · rw [if_pos hz]
        exact mul_nonneg (hpw ω) (hr _)
      · rw [if_neg hz]
  refine hle.trans (le_of_eq ?_)
  rw [group_by_last (t := t)]
  refine Finset.sum_congr rfl fun p' _ => ?_
  rw [← path_pow Q t z p', Finset.sum_mul]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hlast : ω (Fin.last t) = p'
  · rw [if_pos hlast]
    by_cases hz : ω 0 = z
    · rw [if_pos hz, if_pos ⟨hz, hlast⟩, hlast]
    · rw [if_neg hz, if_neg (fun hc => hz hc.1), zero_mul]
  · rw [if_neg hlast, if_neg (fun hc => hlast hc.2), zero_mul]

end Colorings

end

end MarkovMixing

open MarkovMixing

theorem solution {Vv : Type*} [Fintype Vv] [DecidableEq Vv] [Nonempty Vv]
    (G : SimpleGraph Vv) [DecidableRel G.Adj] (q : ℕ)
    (hq : 3 * G.maxDegree < q) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (mixingTime (coloringMetropolis G q)
        (uniformDist {c : Vv → Fin q // IsProperColoring G c}) ε : ℝ) ≤
      (1 - 3 * (G.maxDegree : ℝ) / q)⁻¹ * (Fintype.card Vv) *
        (Real.log (Fintype.card Vv) + Real.log ε⁻¹) + 1 := by
  classical
  have hq0 : 0 < q := by omega
  have hN : 0 < Fintype.card Vv := Fintype.card_pos
  have hNr : (0 : ℝ) < (Fintype.card Vv : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (Fintype.card Vv : ℝ) := by exact_mod_cast hN
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  obtain ⟨c0, hc0⟩ := exists_proper G q (by omega)
  haveI hne : Nonempty {c : Vv → Fin q // IsProperColoring G c} := ⟨⟨c0, hc0⟩⟩
  have hP := metro_stochastic G hq0 hN
  have hpi := metro_stationary G hq0 hN hne
  set cc : ℝ := 1 - 3 * (G.maxDegree : ℝ) / q with hccdef
  have hcc0 : 0 < cc := by
    have h3 : 3 * (G.maxDegree : ℝ) < (q : ℝ) := by exact_mod_cast hq
    rw [hccdef, sub_pos, div_lt_one hqr]
    exact h3
  have hcc1 : cc ≤ 1 := by
    have : 0 ≤ 3 * (G.maxDegree : ℝ) / q := by positivity
    rw [hccdef]; linarith
  set kap : ℝ := 1 - cc / (Fintype.card Vv : ℝ) with hkapdef
  have hkap0 : 0 ≤ kap := by
    have h1 : cc / (Fintype.card Vv : ℝ) ≤ 1 := by
      rw [div_le_one hNr]; linarith
    rw [hkapdef]; linarith
  have hstepQ : ∀ (a b : {c : Vv → Fin q // IsProperColoring G c}) (p : {c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c}),
      ∑ p', Qc G a b p p' * rhoP G p' ≤ kap * rhoP G p := by
    intro a b p
    rw [hkapdef, hccdef]
    exact Qc_contract G hq0 hN a b p
  have htail : ∀ (t : ℕ) (p : {c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c}),
      setAvoidTailProb (Qc G p.1 p.2) p (pairDiagonal {c : Vv → Fin q // IsProperColoring G c}) t
        ≤ kap ^ t * (Fintype.card Vv : ℝ) := by
    intro t p
    have hQst : IsStochastic (Qc G p.1 p.2) := (Qc_markovian G hq0 hN p.1 p.2).1
    calc setAvoidTailProb (Qc G p.1 p.2) p (pairDiagonal {c : Vv → Fin q // IsProperColoring G c}) t
        ≤ ∑ p' : {c : Vv → Fin q // IsProperColoring G c} × {c : Vv → Fin q // IsProperColoring G c}, ((Qc G p.1 p.2) ^ t) p p' * rhoP G p' :=
          tail_le _ hQst (rhoP G) (rhoP_nonneg G) (pairDiagonal {c : Vv → Fin q // IsProperColoring G c})
            (fun w hw => rhoP_off_diag G w hw) p t
      _ ≤ kap ^ t * rhoP G p :=
          pow_contract _ hQst (rhoP G) (rhoP_nonneg G) kap hkap0 (hstepQ p.1 p.2) t p
      _ ≤ kap ^ t * (Fintype.card Vv : ℝ) :=
          mul_le_mul_of_nonneg_left (rhoP_le G p) (by positivity)
  have hd : ∀ t : ℕ,
      distStationary (coloringMetropolis G q) (uniformDist {c : Vv → Fin q // IsProperColoring G c}) t
        ≤ kap ^ t * (Fintype.card Vv : ℝ) := by
    intro t
    have hcb := (coupling_bound (coloringMetropolis G q) hP (uniformDist {c : Vv → Fin q // IsProperColoring G c}) hpi
      (fun a b => Qc G a b) (fun a b => Qc_markovian G hq0 hN a b) t).2
    exact hcb.trans (ciSup_le fun p => htail t p)
  set L : ℝ := Real.log (Fintype.card Vv) + Real.log ε⁻¹ with hLdef
  have hL0 : 0 ≤ L := by
    have h1 : 0 ≤ Real.log (Fintype.card Vv) := Real.log_nonneg hN1
    have h2 : 0 ≤ Real.log ε⁻¹ := Real.log_nonneg (by rw [le_inv_comm₀ (by norm_num) hε]; simpa using hε1)
    rw [hLdef]; linarith
  set X : ℝ := (Fintype.card Vv : ℝ) / cc * L with hXdef
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  set T : ℕ := ⌈X⌉₊ with hTdef
  have hTX : X ≤ (T : ℝ) := Nat.le_ceil X
  have hdT : distStationary (coloringMetropolis G q) (uniformDist {c : Vv → Fin q // IsProperColoring G c}) T ≤ ε := by
    refine (hd T).trans ?_
    have hkexp : kap ≤ Real.exp (-(cc / (Fintype.card Vv : ℝ))) := by
      have := Real.add_one_le_exp (-(cc / (Fintype.card Vv : ℝ)))
      rw [hkapdef]; linarith
    have hpow : kap ^ T ≤ Real.exp (-(cc / (Fintype.card Vv : ℝ))) ^ T :=
      pow_le_pow_left₀ hkap0 hkexp T
    have hE : Real.exp (-(cc / (Fintype.card Vv : ℝ))) ^ T
        = Real.exp ((T : ℝ) * -(cc / (Fintype.card Vv : ℝ))) := by
      rw [Real.exp_nat_mul]
    have hle : (T : ℝ) * -(cc / (Fintype.card Vv : ℝ)) ≤ -L := by
      have h1 : L ≤ (T : ℝ) * (cc / (Fintype.card Vv : ℝ)) := by
        have h2 : X * (cc / (Fintype.card Vv : ℝ)) ≤ (T : ℝ) * (cc / (Fintype.card Vv : ℝ)) :=
          mul_le_mul_of_nonneg_right hTX (by positivity)
        have h3 : X * (cc / (Fintype.card Vv : ℝ)) = L := by
          rw [hXdef]; field_simp
        linarith [h2, h3.symm.le, h3.le]
      linarith [h1]
    have hmono : Real.exp ((T : ℝ) * -(cc / (Fintype.card Vv : ℝ))) ≤ Real.exp (-L) :=
      Real.exp_le_exp.mpr hle
    have hexp : Real.exp (-L) * (Fintype.card Vv : ℝ) = ε := by
      rw [hLdef, Real.log_inv,
        show -(Real.log (Fintype.card Vv) + -Real.log ε)
          = Real.log ε - Real.log (Fintype.card Vv) from by ring,
        Real.exp_sub, Real.exp_log hε, Real.exp_log hNr]
      field_simp
    calc kap ^ T * (Fintype.card Vv : ℝ)
        ≤ Real.exp (-L) * (Fintype.card Vv : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hNr)
          rw [hE] at hpow
          exact hpow.trans hmono
      _ = ε := hexp
  have hmix : mixingTime (coloringMetropolis G q) (uniformDist {c : Vv → Fin q // IsProperColoring G c}) ε ≤ T :=
    Nat.sInf_le hdT
  have hTle : (T : ℝ) < X + 1 := Nat.ceil_lt_add_one hX0
  have hfinal : X = (1 - 3 * (G.maxDegree : ℝ) / q)⁻¹ * (Fintype.card Vv) * L := by
    rw [hXdef, ← hccdef]
    field_simp
  have hcast : (mixingTime (coloringMetropolis G q) (uniformDist {c : Vv → Fin q // IsProperColoring G c}) ε : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast hmix
  linarith [hcast, hTle, hfinal.le, hfinal.symm.le]

