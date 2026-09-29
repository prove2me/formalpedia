-- Prove2me | solution 1 for MarkovMixing.torus_mixing
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-23T01:15:58.181488+00:00
-- url     : https://prove2.me/submissions/f267a79e-26ff-4f40-9909-4e5908541038

import Definitions.Def_mm_coupling
import Theorems.Thm_MarkovMixing_coupling_bound
import Theorems.Thm_MarkovMixing_distPairs_submultiplicative
import Theorems.Thm_MarkovMixing_dist_le_distPairs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.ZMod.Basic

/-!
# Mixing of the lazy walk on the torus (LPW Theorem 5.5)
-/

namespace MarkovMixing

noncomputable section
open scoped BigOperators
open Finset

section Generic

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

/-- The sub-probability of surviving outside `S` up to time `t` and being at `p`. -/
private def surv (Q : Matrix W W ℝ) (z : W) (S : Finset W) (t : ℕ) (p : W) : ℝ :=
  ∑ ω : Fin (t + 1) → W,
    if ω 0 = z ∧ (∀ i : Fin (t + 1), ω i ∉ S) ∧ ω (Fin.last t) = p then
      pathWeight Q ω else 0

private lemma surv_sum (Q : Matrix W W ℝ) (z : W) (S : Finset W) (t : ℕ) :
    ∑ p : W, surv Q z S t p = setAvoidTailProb Q z S t := by
  simp only [surv, setAvoidTailProb]
  rw [group_by_last (t := t)]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hl : ω (Fin.last t) = p
  · rw [if_pos hl]
    by_cases hc : ω 0 = z ∧ ∀ i : Fin (t + 1), ω i ∉ S
    · rw [if_pos ⟨hc.1, hc.2, hl⟩, if_pos hc]
    · rw [if_neg hc, if_neg (fun h => hc ⟨h.1, h.2.1⟩)]
  · rw [if_neg hl, if_neg (fun h => hl h.2.2)]

private lemma surv_nonneg {Q : Matrix W W ℝ} (hQ : IsStochastic Q) (z : W) (S : Finset W)
    (t : ℕ) (p : W) : 0 ≤ surv Q z S t p := by
  refine Finset.sum_nonneg fun ω _ => ?_
  split_ifs
  · exact Finset.prod_nonneg fun i _ => hQ.1 _ _
  · exact le_refl 0

private lemma surv_mem {Q : Matrix W W ℝ} (z : W) (S : Finset W) (t : ℕ) {p : W}
    (hp : p ∈ S) : surv Q z S t p = 0 := by
  refine Finset.sum_eq_zero fun ω _ => ?_
  rw [if_neg]
  rintro ⟨-, h2, h3⟩
  exact h2 (Fin.last t) (h3 ▸ hp)

private lemma surv_zero (Q : Matrix W W ℝ) (z : W) (S : Finset W) (p : W) :
    surv Q z S 0 p = if z = p ∧ z ∉ S then (1 : ℝ) else 0 := by
  simp only [surv]
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) W)
      (fun ω : Fin 1 → W => if ω 0 = z ∧ (∀ i : Fin 1, ω i ∉ S) ∧ ω (Fin.last 0) = p then
        pathWeight Q ω else 0)
      (fun v : W => if v = z then (if z = p ∧ z ∉ S then (1 : ℝ) else 0) else 0)]
  · rw [Finset.sum_ite_eq' Finset.univ z]
    simp
  · intro ω
    simp only [pathWeight, Finset.univ_eq_empty, Finset.prod_empty, Equiv.funUnique_apply]
    have hl : (Fin.last 0 : Fin 1) = 0 := rfl
    rw [hl]
    show (if ω 0 = z ∧ (∀ i : Fin 1, ω i ∉ S) ∧ ω 0 = p then (1 : ℝ) else 0)
        = if ω 0 = z then (if z = p ∧ z ∉ S then (1 : ℝ) else 0) else 0
    by_cases h1 : ω 0 = z
    · rw [if_pos h1]
      have hall : (∀ i : Fin 1, ω i ∉ S) ↔ z ∉ S := by
        constructor
        · intro h; rw [← h1]; exact h 0
        · intro h i
          have : i = 0 := Subsingleton.elim i 0
          rw [this, h1]; exact h
      by_cases h2 : z = p ∧ z ∉ S
      · rw [if_pos h2, if_pos ⟨h1, hall.mpr h2.2, by rw [h1, h2.1]⟩]
      · rw [if_neg h2, if_neg]
        rintro ⟨-, hS, hp⟩
        exact h2 ⟨by rw [← h1, hp], hall.mp hS⟩
    · rw [if_neg h1, if_neg]
      rintro ⟨hc, -, -⟩
      exact h1 hc

private lemma surv_succ (Q : Matrix W W ℝ) (z : W) (S : Finset W) (t : ℕ) (p : W) :
    surv Q z S (t + 1) p
      = if p ∈ S then 0 else ∑ z' : W, surv Q z S t z' * Q z' p := by
  by_cases hp : p ∈ S
  · rw [if_pos hp, surv_mem z S (t + 1) hp]
  rw [if_neg hp]
  simp only [surv]
  rw [snoc_sum]
  have key : ∀ (ω : Fin (t + 1) → W) (y : W),
      (if (Fin.snoc ω y : Fin (t + 2) → W) 0 = z ∧
            (∀ i : Fin (t + 2), (Fin.snoc ω y : Fin (t + 2) → W) i ∉ S) ∧
            (Fin.snoc ω y : Fin (t + 2) → W) (Fin.last (t + 1)) = p then
          pathWeight Q (Fin.snoc ω y : Fin (t + 2) → W) else 0)
        = (if ω 0 = z ∧ (∀ i : Fin (t + 1), ω i ∉ S) then (1 : ℝ) else 0) *
            pathWeight Q ω * Q (ω (Fin.last t)) y * (if y = p then (1 : ℝ) else 0) := by
    intro ω y
    have h0 : (Fin.snoc ω y : Fin (t + 2) → W) 0 = ω 0 := by
      have : (0 : Fin (t + 2)) = Fin.castSucc (0 : Fin (t + 1)) := rfl
      rw [this, Fin.snoc_castSucc]
    have hl : (Fin.snoc ω y : Fin (t + 2) → W) (Fin.last (t + 1)) = y := by simp
    have hall : (∀ i : Fin (t + 2), (Fin.snoc ω y : Fin (t + 2) → W) i ∉ S)
        ↔ ((∀ i : Fin (t + 1), ω i ∉ S) ∧ y ∉ S) := by
      constructor
      · intro h
        refine ⟨fun i => ?_, ?_⟩
        · have := h i.castSucc
          rwa [Fin.snoc_castSucc] at this
        · have := h (Fin.last (t + 1))
          rwa [hl] at this
      · rintro ⟨h1, h2⟩ i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨i', hi'⟩ | hi'
        · rw [hi', Fin.snoc_castSucc]; exact h1 i'
        · rw [hi', hl]; exact h2
    rw [h0, hl, pathWeight_snoc]
    simp only [hall]
    have hyS : y = p → y ∉ S := fun h => h ▸ hp
    by_cases hy : y = p
    · by_cases hx : ω 0 = z ∧ ∀ i : Fin (t + 1), ω i ∉ S
      · rw [if_pos ⟨hx.1, ⟨hx.2, hyS hy⟩, hy⟩, if_pos hx, if_pos hy]
        ring
      · rw [if_neg (fun h => hx ⟨h.1, h.2.1.1⟩), if_neg hx]
        ring
    · rw [if_neg (fun h => hy h.2.2), if_neg hy]
      ring
  calc ∑ ω : Fin (t + 1) → W, ∑ y : W, _
      = ∑ ω : Fin (t + 1) → W, ∑ y : W,
          ((if ω 0 = z ∧ (∀ i : Fin (t + 1), ω i ∉ S) then (1 : ℝ) else 0) *
            pathWeight Q ω * Q (ω (Fin.last t)) y * (if y = p then (1 : ℝ) else 0)) :=
        Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun y _ => key ω y
    _ = ∑ ω : Fin (t + 1) → W,
          ((if ω 0 = z ∧ (∀ i : Fin (t + 1), ω i ∉ S) then (1 : ℝ) else 0) *
            pathWeight Q ω * Q (ω (Fin.last t)) p) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        have hc : ∀ y ∈ (Finset.univ : Finset W),
            ((if ω 0 = z ∧ (∀ i : Fin (t + 1), ω i ∉ S) then (1 : ℝ) else 0) *
              pathWeight Q ω * Q (ω (Fin.last t)) y * (if y = p then (1 : ℝ) else 0))
            = if y = p then ((if ω 0 = z ∧ (∀ i : Fin (t + 1), ω i ∉ S) then (1 : ℝ) else 0) *
                pathWeight Q ω * Q (ω (Fin.last t)) p) else 0 := by
          intro y _
          by_cases hy : y = p
          · subst hy; simp
          · simp [hy]
        rw [Finset.sum_congr rfl hc]
        simp
    _ = ∑ z' : W, surv Q z S t z' * Q z' p := by
        rw [group_by_last (t := t)]
        refine Finset.sum_congr rfl fun z' _ => ?_
        simp only [surv, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ω _ => ?_
        by_cases hz : ω (Fin.last t) = z'
        · rw [if_pos hz]
          by_cases hx : ω 0 = z ∧ ∀ i : Fin (t + 1), ω i ∉ S
          · rw [if_pos hx, if_pos ⟨hx.1, hx.2, hz⟩, hz]
            ring
          · rw [if_neg hx, if_neg (fun h => hx ⟨h.1, h.2.1⟩)]
            ring
        · rw [if_neg hz, if_neg (fun h => hz h.2.2), zero_mul]

/-- A Lyapunov function that decreases by at least `cst` off the target set bounds
the tail of the hitting time by Markov's inequality. -/
private lemma lyapunov_tail (Q : Matrix W W ℝ) (hQ : IsStochastic Q) (S : Finset W)
    (H : W → ℝ) (hH : ∀ w, 0 ≤ H w) (cst : ℝ) (hc : 0 < cst)
    (hdrop : ∀ w : W, w ∉ S → ∑ p : W, Q w p * H p ≤ H w - cst)
    (z : W) (t : ℕ) (ht : 0 < t) :
    setAvoidTailProb Q z S t ≤ H z / (cst * t) := by
  set R : ℕ → ℝ := fun u => ∑ p : W, surv Q z S u p with hR
  set V : ℕ → ℝ := fun u => ∑ p : W, surv Q z S u p * H p with hV
  have hsnn : ∀ u p, 0 ≤ surv Q z S u p := fun u p => surv_nonneg hQ z S u p
  have hVnn : ∀ u, 0 ≤ V u := fun u =>
    Finset.sum_nonneg fun p _ => mul_nonneg (hsnn u p) (hH p)
  have hRnn : ∀ u, 0 ≤ R u := fun u => Finset.sum_nonneg fun p _ => hsnn u p
  have hle : ∀ u p, surv Q z S (u + 1) p ≤ ∑ z' : W, surv Q z S u z' * Q z' p := by
    intro u p
    rw [surv_succ]
    split_ifs with hp
    · exact Finset.sum_nonneg fun z' _ => mul_nonneg (hsnn u z') (hQ.1 _ _)
    · exact le_refl _
  have hRmono : ∀ u, R (u + 1) ≤ R u := by
    intro u
    calc R (u + 1) ≤ ∑ p : W, ∑ z' : W, surv Q z S u z' * Q z' p :=
          Finset.sum_le_sum fun p _ => hle u p
      _ = ∑ z' : W, surv Q z S u z' * ∑ p : W, Q z' p := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun z' _ => (Finset.mul_sum _ _ _).symm
      _ = R u := by
          refine Finset.sum_congr rfl fun z' _ => ?_
          rw [hQ.2 z', mul_one]
  have hVstep : ∀ u, V (u + 1) ≤ V u - cst * R u := by
    intro u
    calc V (u + 1) ≤ ∑ p : W, (∑ z' : W, surv Q z S u z' * Q z' p) * H p :=
          Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_right (hle u p) (hH p)
      _ = ∑ z' : W, surv Q z S u z' * ∑ p : W, Q z' p * H p := by
          rw [Finset.sum_congr rfl (fun p _ => Finset.sum_mul _ _ _), Finset.sum_comm]
          refine Finset.sum_congr rfl fun z' _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => by ring
      _ ≤ ∑ z' : W, surv Q z S u z' * (H z' - cst) := by
          refine Finset.sum_le_sum fun z' _ => ?_
          by_cases hz' : z' ∈ S
          · rw [surv_mem z S u hz']
            simp
          · exact mul_le_mul_of_nonneg_left (hdrop z' hz') (hsnn u z')
      _ = V u - cst * R u := by
          rw [hV, hR, Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun z' _ => by ring
  have hV0 : V 0 ≤ H z := by
    have : ∀ p ∈ (Finset.univ : Finset W), surv Q z S 0 p * H p
        = if z = p then (if z ∉ S then H p else 0) else 0 := by
      intro p _
      rw [surv_zero]
      by_cases h1 : z = p
      · by_cases h2 : z ∉ S <;> simp [h1, h2]
      · simp [h1]
    show (∑ p : W, surv Q z S 0 p * H p) ≤ H z
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq Finset.univ z]
    simp only [Finset.mem_univ, if_true]
    split_ifs with hzS
    · exact hH z
    · exact le_refl (H z)
  have hVbd : ∀ u, V u ≤ H z - cst * ∑ s ∈ Finset.range u, R s := by
    intro u
    induction u with
    | zero => simpa using hV0
    | succ u ih =>
      have := hVstep u
      rw [Finset.sum_range_succ, mul_add]
      linarith
  have hRadd : ∀ s u : ℕ, R (s + u) ≤ R s := by
    intro s u
    induction u with
    | zero => exact le_refl _
    | succ u ih => exact le_trans (hRmono (s + u)) ih
  have hRle : ∀ s, s ≤ t → R t ≤ R s := by
    intro s hs
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
    rw [hk]
    exact hRadd s k
  have hsum : (t : ℝ) * R t ≤ ∑ s ∈ Finset.range t, R s := by
    calc (t : ℝ) * R t = ∑ _s ∈ Finset.range t, R t := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ s ∈ Finset.range t, R s :=
          Finset.sum_le_sum fun s hs => hRle s (le_of_lt (Finset.mem_range.mp hs))
  have hfin : cst * ((t : ℝ) * R t) ≤ H z := by
    have h1 := hVbd t
    have h2 := hVnn t
    nlinarith [hsum, hc.le]
  have hgoal : (∑ p : W, surv Q z S t p) = R t := rfl
  rw [← surv_sum Q z S t, hgoal, le_div_iff₀ (by positivity)]
  have hring : R t * (cst * (t : ℝ)) = cst * ((t : ℝ) * R t) := by ring
  rw [hring]
  exact hfin

end Generic

/-! ## Chains driven by a uniform proposal -/

section Uniform

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Pr : Type*} [Fintype Pr] [DecidableEq Pr]

private lemma sum_div_const {α : Type*} (s : Finset α) (f : α → ℝ) (c : ℝ) :
    (∑ i ∈ s, f i) / c = ∑ i ∈ s, f i / c := by
  simp [div_eq_mul_inv, Finset.sum_mul]

private lemma push_sum (φ : Pr → W) (g : W → ℝ) :
    ∑ q : W, ((univ.filter fun w : Pr => φ w = q).card : ℝ) * g q
      = ∑ w : Pr, g (φ w) := by
  classical
  have h := Finset.sum_fiberwise_of_maps_to
    (s := (univ : Finset Pr)) (t := (univ : Finset W)) (g := φ)
    (f := fun w : Pr => g (φ w)) (fun w _ => Finset.mem_univ _)
  rw [← h]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => g q) ?_, Finset.sum_const, nsmul_eq_mul]
  intro w hw
  simp only [Finset.mem_filter] at hw
  rw [hw.2]

/-- The transition matrix obtained by applying a uniformly chosen proposal `w : Pr`
to the current state through the map `f`. -/
private def ker (f : W → Pr → W) : Matrix W W ℝ :=
  fun p q => ((univ.filter fun w : Pr => f p w = q).card : ℝ) / (Fintype.card Pr : ℝ)

private lemma ker_sum (f : W → Pr → W) (p : W) (g : W → ℝ) :
    ∑ q : W, ker f p q * g q = (∑ w : Pr, g (f p w)) / (Fintype.card Pr : ℝ) := by
  simp only [ker, div_mul_eq_mul_div]
  rw [← sum_div_const, push_sum]

private lemma card_pos_real [Nonempty Pr] : (0 : ℝ) < (Fintype.card Pr : ℝ) := by
  exact_mod_cast Fintype.card_pos

private lemma ker_stochastic [Nonempty Pr] (f : W → Pr → W) : IsStochastic (ker f) := by
  refine ⟨fun p q => by unfold ker; positivity, fun p => ?_⟩
  have h := ker_sum f p (fun _ => (1 : ℝ))
  simp only [mul_one] at h
  rw [h]
  have hM : (0 : ℝ) < (Fintype.card Pr : ℝ) := card_pos_real
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  field_simp

private lemma ker_marg1 (f : W → Pr → W) (σ : W × W → Pr → Pr) (p : W × W) (x' : W) :
    ∑ y' : W, ker (fun r w => (f r.1 w, f r.2 (σ r w))) p (x', y') = ker f p.1 x' := by
  classical
  simp only [ker]
  rw [← sum_div_const]
  congr 1
  have hh := Finset.card_eq_sum_card_fiberwise
    (f := fun w : Pr => f p.2 (σ p w))
    (s := (univ.filter fun w : Pr => f p.1 w = x'))
    (t := (univ : Finset W)) (fun w _ => Finset.mem_univ _)
  rw [hh, Nat.cast_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  congr 2
  rw [Finset.filter_filter]
  exact Finset.filter_congr fun w _ => by simp [Prod.ext_iff]

private lemma ker_marg2 (f : W → Pr → W) (σ : W × W → Pr → Pr)
    (hσ : ∀ r : W × W, Function.Bijective (σ r)) (p : W × W) (y' : W) :
    ∑ x' : W, ker (fun r w => (f r.1 w, f r.2 (σ r w))) p (x', y') = ker f p.2 y' := by
  classical
  simp only [ker]
  rw [← sum_div_const]
  congr 1
  have hcard : (univ.filter fun w : Pr => f p.2 (σ p w) = y').card
      = (univ.filter fun w : Pr => f p.2 w = y').card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact Equiv.sum_comp (Equiv.ofBijective (σ p) (hσ p))
      (fun w : Pr => if f p.2 w = y' then 1 else 0)
  have hh := Finset.card_eq_sum_card_fiberwise
    (f := fun w : Pr => f p.1 w)
    (s := (univ.filter fun w : Pr => f p.2 (σ p w) = y'))
    (t := (univ : Finset W)) (fun w _ => Finset.mem_univ _)
  rw [← hcard, hh, Nat.cast_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  congr 2
  rw [Finset.filter_filter]
  exact Finset.filter_congr fun w _ => by simp [Prod.ext_iff, and_comm]

private lemma ker_diag (f : W → Pr → W) (σ : W × W → Pr → Pr)
    (hd : ∀ x : W, ∀ w : Pr, f x (σ (x, x) w) = f x w) (x : W) (r : W × W) (hr : r.1 ≠ r.2) :
    ker (fun s w => (f s.1 w, f s.2 (σ s w))) (x, x) r = 0 := by
  classical
  simp only [ker]
  have hE : (univ.filter fun w : Pr => (f x w, f x (σ (x, x) w)) = r) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr fun w _ h => hr ?_
    rw [← congrArg Prod.fst h, ← congrArg Prod.snd h, hd]
  rw [hE]
  simp

private lemma ker_markovian [Nonempty Pr] (f : W → Pr → W) (σ : W × W → Pr → Pr)
    (hσ : ∀ r : W × W, Function.Bijective (σ r))
    (hd : ∀ x : W, ∀ w : Pr, f x (σ (x, x) w) = f x w) :
    IsMarkovianCoupling (ker f) (ker fun s w => (f s.1 w, f s.2 (σ s w))) :=
  ⟨ker_stochastic _, ker_marg1 f σ, ker_marg2 f σ hσ, ker_diag f σ hd⟩

private lemma ker_col_sum [Nonempty Pr] (f : W → Pr → W)
    (hf : ∀ w : Pr, Function.Bijective fun x : W => f x w) (q : W) :
    ∑ p : W, ker f p q = 1 := by
  classical
  have hM : (0 : ℝ) < (Fintype.card Pr : ℝ) := card_pos_real
  have key : (∑ p : W, (univ.filter fun w : Pr => f p w = q).card) = Fintype.card Pr := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    have hin : ∀ w : Pr, (∑ p : W, if f p w = q then 1 else 0) = 1 := by
      intro w
      obtain ⟨p₀, hp₀⟩ := (hf w).surjective q
      rw [Finset.sum_eq_single p₀]
      · rw [if_pos hp₀]
      · intro b _ hb
        rw [if_neg]
        intro h
        exact hb ((hf w).injective (h.trans hp₀.symm))
      · intro h; exact absurd (Finset.mem_univ p₀) h
    rw [Finset.sum_congr rfl fun w _ => hin w]
    simp
  simp only [ker]
  rw [← sum_div_const, ← Nat.cast_sum, key]
  field_simp

private lemma ker_uniform_stationary [Nonempty W] [Nonempty Pr] (f : W → Pr → W)
    (hf : ∀ w : Pr, Function.Bijective fun x : W => f x w) :
    IsStationary (ker f) (uniformDist W) := by
  have hW : (0 : ℝ) < (Fintype.card W : ℝ) := by
    exact_mod_cast Fintype.card_pos
  refine ⟨⟨fun x => by unfold uniformDist; positivity, ?_⟩, ?_⟩
  · simp only [uniformDist, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  · ext q
    simp only [Matrix.vecMul, dotProduct, uniformDist]
    rw [← Finset.mul_sum, ker_col_sum f hf q, mul_one]

end Uniform

/-! ## The lazy walk on the torus as a uniform-proposal chain -/

section Torus

variable {d n : ℕ}

/-- The step `+1` or `-1` selected by a sign bit. -/
private def sgnZ (n : ℕ) (s : Bool) : ZMod n := if s then 1 else -1

private lemma sgnZ_not (n : ℕ) (s : Bool) : sgnZ n (!s) = -sgnZ n s := by
  cases s <;> simp [sgnZ]

private lemma sgnZ_ne_zero (hn : 2 ≤ n) (s : Bool) : sgnZ n s ≠ (0 : ZMod n) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  cases s <;> simp [sgnZ]

/-- Move the `j`-th coordinate by `±1`. -/
private def upd (x : Fin d → ZMod n) (j : Fin d) (s : Bool) : Fin d → ZMod n :=
  Function.update x j (x j + sgnZ n s)

/-- One lazy step: with the bit `w.2.2` set, move coordinate `w.1` by `±1`. -/
private def mv (x : Fin d → ZMod n) (w : Fin d × Bool × Bool) : Fin d → ZMod n :=
  if w.2.2 then upd x w.1 w.2.1 else x

private lemma upd_self (x : Fin d → ZMod n) (j : Fin d) (s : Bool) :
    upd x j s j = x j + sgnZ n s := by
  simp [upd]

private lemma upd_ne (x : Fin d → ZMod n) (j : Fin d) (s : Bool) {i : Fin d} (h : i ≠ j) :
    upd x j s i = x i := by
  simp [upd, Function.update_apply, h]

private lemma upd_upd (x : Fin d → ZMod n) (j : Fin d) (s : Bool) :
    upd (upd x j s) j (!s) = x := by
  funext i
  by_cases h : i = j
  · subst h
    rw [upd_self, upd_self, sgnZ_not]
    ring
  · rw [upd_ne _ _ _ h, upd_ne _ _ _ h]

private def flipw (w : Fin d × Bool × Bool) : Fin d × Bool × Bool := (w.1, !w.2.1, w.2.2)

private lemma flipw_flipw (w : Fin d × Bool × Bool) : flipw (flipw w) = w := by
  simp [flipw]

private lemma mv_mv (x : Fin d → ZMod n) (w : Fin d × Bool × Bool) :
    mv (mv x w) (flipw w) = x := by
  simp only [mv, flipw]
  split_ifs with h
  · exact upd_upd x w.1 w.2.1
  · rfl

private lemma mv_bijective (w : Fin d × Bool × Bool) :
    Function.Bijective fun x : Fin d → ZMod n => mv x w := by
  refine Function.bijective_iff_has_inverse.mpr ⟨fun y => mv y (flipw w), fun x => ?_, fun y => ?_⟩
  · exact mv_mv x w
  · have h := mv_mv y (flipw w)
    rwa [flipw_flipw] at h

/-- The number of sign bits realising a given unit step. -/
private def cc (n : ℕ) : ℕ := (univ.filter fun s : Bool => sgnZ n s = (1 : ZMod n)).card

private lemma cc_pos : 0 < cc n := by
  refine Finset.card_pos.mpr ⟨true, ?_⟩
  simp [sgnZ]

private lemma card_sgn (δ : ZMod n) (hδ : δ = 1 ∨ δ = -1) :
    (univ.filter fun s : Bool => sgnZ n s = δ).card = cc n := by
  rcases hδ with h | h
  · subst h; rfl
  · subst h
    have e1 : sgnZ n true = (1 : ZMod n) := rfl
    have e2 : sgnZ n false = (-1 : ZMod n) := rfl
    simp only [cc, Finset.card_filter, Fintype.sum_bool, e1, e2]
    by_cases h1 : (1 : ZMod n) = -1
    · rw [if_pos h1, if_pos h1.symm]; simp
    · rw [if_neg h1, if_neg (Ne.symm h1)]; simp

private lemma cnt2_eq (hn : 2 ≤ n) (x y : Fin d → ZMod n) :
    (univ.filter fun v : Fin d × Bool => upd x v.1 v.2 = y).card
      = if (torusGraph d n).Adj x y then cc n else 0 := by
  classical
  have hupd_iff : ∀ (j : Fin d) (s : Bool), (∀ i : Fin d, i ≠ j → x i = y i) →
      (upd x j s = y ↔ sgnZ n s = y j - x j) := by
    intro j s hoff
    constructor
    · intro h
      have := congrFun h j
      rw [upd_self] at this
      rw [← this]; ring
    · intro h
      funext i
      by_cases hi : i = j
      · subst hi
        rw [upd_self, h]; ring
      · rw [upd_ne _ _ _ hi]; exact hoff i hi
  have h1 : (1 : ZMod n) ≠ 0 := sgnZ_ne_zero hn true
  have h2 : (-1 : ZMod n) ≠ 0 := sgnZ_ne_zero hn false
  by_cases hA : (torusGraph d n).Adj x y
  · rw [if_pos hA]
    obtain ⟨hxy, j, hoff, hj⟩ := hA
    have hdiff : y j - x j = 1 ∨ y j - x j = -1 := by
      rcases hj with h | h
      · left; rw [h]; ring
      · right; rw [h]; ring
    have hjne : y j ≠ x j := by
      intro h
      rcases hdiff with hq | hq <;> rw [h, sub_self] at hq
      · exact h1 hq.symm
      · exact h2 hq.symm
    rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_eq_single j]
    · rw [← card_sgn (y j - x j) hdiff, Finset.card_filter]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases hs : sgnZ n s = y j - x j
      · rw [if_pos ((hupd_iff j s hoff).mpr hs), if_pos hs]
      · rw [if_neg (fun h => hs ((hupd_iff j s hoff).mp h)), if_neg hs]
    · intro j' _ hj'
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [if_neg]
      intro h
      exact hjne (by rw [← h, upd_ne _ _ _ (Ne.symm hj')])
    · intro h; exact absurd (Finset.mem_univ j) h
  · rw [if_neg hA]
    refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun v _ h => hA ?_)
    have hne : ∀ i : Fin d, i ≠ v.1 → x i = y i := by
      intro i hi
      rw [← h, upd_ne _ _ _ hi]
    have hat : y v.1 = x v.1 + sgnZ n v.2 := by rw [← h, upd_self]
    refine ⟨?_, v.1, hne, ?_⟩
    · intro hxy
      apply sgnZ_ne_zero hn v.2
      rw [hxy] at hat
      linear_combination -hat
    · by_cases hv : v.2 = true
      · left
        rw [hat, hv]
        simp [sgnZ]
      · right
        have hv' : v.2 = false := by simpa using hv
        rw [hat, hv']
        show x v.1 + (-1 : ZMod n) = x v.1 - 1
        ring

variable [NeZero n]

private lemma cnt2_total (x : Fin d → ZMod n) :
    ∑ y : Fin d → ZMod n, (univ.filter fun v : Fin d × Bool => upd x v.1 v.2 = y).card
      = 2 * d := by
  classical
  have hh := Finset.card_eq_sum_card_fiberwise
    (f := fun v : Fin d × Bool => upd x v.1 v.2)
    (s := (univ : Finset (Fin d × Bool))) (t := (univ : Finset (Fin d → ZMod n)))
    (fun v _ => Finset.mem_univ _)
  rw [← hh, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

private lemma degree_mul (hn : 2 ≤ n) (x : Fin d → ZMod n) :
    (torusGraph d n).degree x * cc n = 2 * d := by
  classical
  rw [← cnt2_total x, Finset.sum_congr rfl (fun y _ => cnt2_eq hn x y), ← Finset.sum_filter,
    Finset.sum_const, smul_eq_mul]
  congr 1
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]

private lemma cnt_split (x y : Fin d → ZMod n) :
    (univ.filter fun w : Fin d × Bool × Bool => mv x w = y).card
      = 2 * d * (if x = y then 1 else 0)
        + (univ.filter fun v : Fin d × Bool => upd x v.1 v.2 = y).card := by
  classical
  have hstep : ∀ (j : Fin d) (s : Bool),
      (∑ b : Bool, if mv x (j, s, b) = y then 1 else 0)
        = (if upd x j s = y then 1 else 0) + (if x = y then 1 else 0) := by
    intro j s
    rw [Fintype.sum_bool]
    rfl
  rw [Finset.card_filter, Finset.card_filter]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun s _ => hstep j s))]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_bool, smul_eq_mul]
  ring

private lemma card_prop : Fintype.card (Fin d × Bool × Bool) = 4 * d := by
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

/-- The lazy walk on the torus is exactly the chain driven by a uniform proposal
`(coordinate, sign, move-or-stay)`. -/
private lemma lazy_eq_ker (hd0 : 0 < d) (hn : 2 ≤ n) :
    lazy (graphWalk (torusGraph d n)) = ker (mv : (Fin d → ZMod n) → _ → _) := by
  classical
  ext x y
  have hdeg := degree_mul hn x
  have hccpos : 0 < cc n := cc_pos
  have hdegpos : 0 < (torusGraph d n).degree x := by
    rcases Nat.eq_zero_or_pos ((torusGraph d n).degree x) with h | h
    · rw [h, zero_mul] at hdeg; omega
    · exact h
  have hdR : ((torusGraph d n).degree x : ℝ) * (cc n : ℝ) = 2 * (d : ℝ) := by
    exact_mod_cast hdeg
  have hd0R : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hdegR : (0 : ℝ) < ((torusGraph d n).degree x : ℝ) := by exact_mod_cast hdegpos
  have hccR : (0 : ℝ) < (cc n : ℝ) := by exact_mod_cast hccpos
  simp only [lazy, ker, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, graphWalk,
    smul_eq_mul, cnt_split, cnt2_eq hn, card_prop]
  push_cast
  by_cases hxy : x = y
  · have hnadj : ¬ (torusGraph d n).Adj x y := fun h => h.ne hxy
    simp only [if_pos hxy, if_neg hnadj]
    field_simp
    ring
  · simp only [if_neg hxy]
    by_cases hA : (torusGraph d n).Adj x y
    · simp only [if_pos hA]
      have h4 : (4 : ℝ) * (d : ℝ) = 2 * ((torusGraph d n).degree x : ℝ) * (cc n : ℝ) := by
        linarith [hdR]
      rw [h4]
      field_simp
      ring
    · simp only [if_neg hA]
      simp

/-! ### The coupling -/

/-- The coupling proposal map: the two chains use the same coordinate and the same
sign; the lazy bit is shared when the coordinate agrees and flipped otherwise, so
that a disagreeing coordinate is always moved in exactly one of the two chains. -/
private def sig (p : (Fin d → ZMod n) × (Fin d → ZMod n)) (w : Fin d × Bool × Bool) :
    Fin d × Bool × Bool :=
  (w.1, w.2.1, if p.1 w.1 = p.2 w.1 then w.2.2 else !w.2.2)

private lemma sig_sig (p : (Fin d → ZMod n) × (Fin d → ZMod n)) (w : Fin d × Bool × Bool) :
    sig p (sig p w) = w := by
  simp only [sig]
  split_ifs with h <;> simp

private lemma sig_bijective (p : (Fin d → ZMod n) × (Fin d → ZMod n)) :
    Function.Bijective (sig p) :=
  Function.bijective_iff_has_inverse.mpr ⟨sig p, fun w => sig_sig p w, fun w => sig_sig p w⟩

private lemma sig_diag (x : Fin d → ZMod n) (w : Fin d × Bool × Bool) :
    mv x (sig (x, x) w) = mv x w := by
  simp [sig]

/-- The coupled pair chain. -/
private def Qcpl (d n : ℕ) [NeZero n] :
    Matrix ((Fin d → ZMod n) × (Fin d → ZMod n)) ((Fin d → ZMod n) × (Fin d → ZMod n)) ℝ :=
  ker fun r w => (mv r.1 w, mv r.2 (sig r w))

private lemma Qcpl_markovian (hd0 : 0 < d) (hn : 2 ≤ n) :
    IsMarkovianCoupling (lazy (graphWalk (torusGraph d n))) (Qcpl d n) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  rw [lazy_eq_ker hd0 hn]
  exact ker_markovian mv sig sig_bijective sig_diag

/-! ### The Lyapunov function -/

/-- `h(a) = a(n − a)`, which drops by exactly `1` in one symmetric step. -/
private def hz (n : ℕ) (a : ZMod n) : ℝ := (a.val : ℝ) * ((n : ℝ) - (a.val : ℝ))

private lemma hz_nonneg (a : ZMod n) : 0 ≤ hz n a := by
  have h : a.val < n := ZMod.val_lt a
  have h1 : ((a.val : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h.le
  have h2 : (0 : ℝ) ≤ ((a.val : ℕ) : ℝ) := Nat.cast_nonneg _
  simp only [hz]
  nlinarith

private lemma hz_le (a : ZMod n) : hz n a ≤ (n : ℝ) ^ 2 / 4 := by
  simp only [hz]
  nlinarith [sq_nonneg ((n : ℝ) - 2 * ((a.val : ℕ) : ℝ))]

private lemma hz_step (hn : 2 ≤ n) (a : ZMod n) (ha : a ≠ 0) :
    hz n (a + 1) + hz n (a - 1) = 2 * hz n a - 2 := by
  have hcast : ((a.val : ℕ) : ZMod n) = a := ZMod.natCast_zmod_val a
  have hvlt : a.val < n := ZMod.val_lt a
  have hv1 : 1 ≤ a.val := by
    rcases Nat.eq_zero_or_pos a.val with h | h
    · exact absurd (by rw [← hcast, h]; simp) ha
    · exact h
  have hB : a - 1 = ((a.val - 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_sub hv1, Nat.cast_one, hcast]
  have hA : a + 1 = ((a.val + 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_add, Nat.cast_one, hcast]
  have hvB : (a - 1).val = a.val - 1 := by
    rw [hB, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (by omega)
  have hcB : (((a.val - 1 : ℕ)) : ℝ) = ((a.val : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub hv1, Nat.cast_one]
  by_cases hlast : a.val + 1 = n
  · have hvA : (a + 1).val = 0 := by
      rw [hA, ZMod.val_natCast, hlast, Nat.mod_self]
    have hNV : (n : ℝ) = ((a.val : ℕ) : ℝ) + 1 := by exact_mod_cast hlast.symm
    simp only [hz, hvA, hvB, hcB, Nat.cast_zero]
    rw [hNV]
    ring
  · have hvA : (a + 1).val = a.val + 1 := by
      rw [hA, ZMod.val_natCast]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [hz, hvA, hvB, hcB, Nat.cast_add, Nat.cast_one]
    ring

private lemma hz_pair (hn : 2 ≤ n) (a : ZMod n) (ha : a ≠ 0) (e : ZMod n)
    (he : e = 1 ∨ e = -1) : hz n (a + e) + hz n (a + -e) = 2 * hz n a - 2 := by
  have h := hz_step hn a ha
  have hsub : a - 1 = a + -1 := by ring
  rw [hsub] at h
  rcases he with rfl | rfl
  · exact h
  · rw [neg_neg]; linarith [h]

/-- The total circular distance between the two coordinates. -/
private def Hfun (p : (Fin d → ZMod n) × (Fin d → ZMod n)) : ℝ :=
  ∑ j : Fin d, hz n (p.1 j - p.2 j)

private lemma Hfun_nonneg (p : (Fin d → ZMod n) × (Fin d → ZMod n)) : 0 ≤ Hfun p :=
  Finset.sum_nonneg fun j _ => hz_nonneg _

private lemma Hfun_le (p : (Fin d → ZMod n) × (Fin d → ZMod n)) :
    Hfun p ≤ (d : ℝ) * (n : ℝ) ^ 2 / 4 := by
  calc Hfun p ≤ ∑ _j : Fin d, (n : ℝ) ^ 2 / 4 :=
        Finset.sum_le_sum fun j _ => hz_le _
    _ = (d : ℝ) * (n : ℝ) ^ 2 / 4 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

private lemma Hfun_pair (x y : Fin d → ZMod n) (j : Fin d) (c1 c2 : ZMod n) :
    Hfun ((Function.update x j c1 : Fin d → ZMod n), (Function.update y j c2 : Fin d → ZMod n))
      = Hfun (x, y) - hz n (x j - y j) + hz n (c1 - c2) := by
  simp only [Hfun]
  rw [← Finset.add_sum_erase _
      (fun i => hz n (Function.update x j c1 i - Function.update y j c2 i)) (Finset.mem_univ j),
    ← Finset.add_sum_erase _ (fun i => hz n (x i - y i)) (Finset.mem_univ j)]
  have herase : ∑ i ∈ univ.erase j,
      hz n (Function.update x j c1 i - Function.update y j c2 i)
        = ∑ i ∈ univ.erase j, hz n (x i - y i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    rw [Function.update_apply, Function.update_apply, if_neg hij, if_neg hij]
  rw [herase, Function.update_self, Function.update_self]
  ring

private lemma Hfun_upd (x y : Fin d → ZMod n) (j : Fin d) (e1 e2 : ZMod n) :
    Hfun ((Function.update x j (x j + e1) : Fin d → ZMod n),
        (Function.update y j (y j + e2) : Fin d → ZMod n))
      = Hfun (x, y) - hz n (x j - y j) + hz n (x j - y j + (e1 - e2)) := by
  rw [Hfun_pair]
  congr 2
  ring

private lemma mv_as_upd (x : Fin d → ZMod n) (j : Fin d) (s b : Bool) :
    mv x (j, s, b) = Function.update x j (x j + (if b = true then sgnZ n s else 0)) := by
  by_cases hb : b = true
  · rw [if_pos hb]
    show (if b = true then upd x j s else x) = _
    rw [if_pos hb, upd]
  · rw [if_neg hb]
    show (if b = true then upd x j s else x) = _
    rw [if_neg hb, add_zero, Function.update_eq_self]

private lemma inner_sum (hn : 2 ≤ n) (x y : Fin d → ZMod n) (j : Fin d) :
    (∑ s : Bool, ∑ b : Bool, Hfun (mv x (j, s, b), mv y (sig (x, y) (j, s, b))))
      = 4 * Hfun (x, y) - (if x j = y j then 0 else 4) := by
  by_cases hj : x j = y j
  · rw [if_pos hj]
    have hsame : ∀ s b : Bool,
        Hfun (mv x (j, s, b), mv y (sig (x, y) (j, s, b))) = Hfun (x, y) := by
      intro s b
      have h1 : sig (x, y) (j, s, b) = (j, s, b) := by
        simp only [sig]
        rw [if_pos hj]
      rw [h1, mv_as_upd, mv_as_upd, Hfun_upd, sub_self, add_zero]
      ring
    rw [Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun b _ => hsame s b]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
    push_cast
    ring
  · rw [if_neg hj]
    have hD : x j - y j ≠ 0 := sub_ne_zero.mpr hj
    have hexpT : ∀ s : Bool, Hfun (mv x (j, s, true), mv y (sig (x, y) (j, s, true)))
        = Hfun (x, y) - hz n (x j - y j) + hz n (x j - y j + sgnZ n s) := by
      intro s
      have h1 : sig (x, y) (j, s, true) = (j, s, false) := by
        simp only [sig]
        rw [if_neg hj]
        rfl
      rw [h1, mv_as_upd, mv_as_upd, Hfun_upd]
      norm_num
    have hexpF : ∀ s : Bool, Hfun (mv x (j, s, false), mv y (sig (x, y) (j, s, false)))
        = Hfun (x, y) - hz n (x j - y j) + hz n (x j - y j + -sgnZ n s) := by
      intro s
      have h1 : sig (x, y) (j, s, false) = (j, s, true) := by
        simp only [sig]
        rw [if_neg hj]
        rfl
      rw [h1, mv_as_upd, mv_as_upd, Hfun_upd]
      norm_num
    have hb : ∀ s : Bool,
        (∑ b : Bool, Hfun (mv x (j, s, b), mv y (sig (x, y) (j, s, b))))
          = 2 * Hfun (x, y) - 2 := by
      intro s
      rw [Fintype.sum_bool, hexpT s, hexpF s]
      have hp := hz_pair hn (x j - y j) hD (sgnZ n s) (by cases s <;> simp [sgnZ])
      linarith
    rw [Fintype.sum_bool, hb true, hb false]
    ring

/-! ### The one-step drop and the coupling-time bound -/

private lemma Qcpl_drop (hd0 : 0 < d) (hn : 2 ≤ n)
    (p : (Fin d → ZMod n) × (Fin d → ZMod n)) (hp : p ∉ pairDiagonal (Fin d → ZMod n)) :
    ∑ p' : (Fin d → ZMod n) × (Fin d → ZMod n), Qcpl d n p p' * Hfun p'
      ≤ Hfun p - 1 / (d : ℝ) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  obtain ⟨x, y⟩ := p
  have hne : x ≠ y := by
    intro h
    exact hp (by simp [pairDiagonal, h])
  rw [Qcpl, ker_sum]
  have hexp : (∑ w : Fin d × Bool × Bool, Hfun (mv x w, mv y (sig (x, y) w)))
      = ∑ _j : Fin d, (4 * Hfun (x, y)) - ∑ j : Fin d, (if x j = y j then (0 : ℝ) else 4) := by
    rw [← Finset.sum_sub_distrib, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_prod_type]
    exact inner_sum hn x y j
  have hge : (4 : ℝ) ≤ ∑ j : Fin d, (if x j = y j then (0 : ℝ) else 4) := by
    have hcount : ∃ j : Fin d, x j ≠ y j := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    obtain ⟨j0, hj0⟩ := hcount
    calc (4 : ℝ) = (if x j0 = y j0 then (0 : ℝ) else 4) := by rw [if_neg hj0]
      _ ≤ ∑ j : Fin d, (if x j = y j then (0 : ℝ) else 4) :=
          Finset.single_le_sum (f := fun j : Fin d => if x j = y j then (0 : ℝ) else 4)
            (fun j _ => by dsimp only; split_ifs <;> norm_num) (Finset.mem_univ j0)
  rw [hexp, card_prop, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [div_le_iff₀ (by push_cast; positivity)]
  have hcalc : (Hfun (x, y) - 1 / (d : ℝ)) * (((4 * d : ℕ) : ℝ))
      = (d : ℝ) * (4 * Hfun (x, y)) - 4 := by
    push_cast
    field_simp
    try ring
  rw [hcalc]
  linarith

private lemma tail_quarter (hd0 : 0 < d) (hn : 2 ≤ n)
    (p : (Fin d → ZMod n) × (Fin d → ZMod n)) :
    setAvoidTailProb (Qcpl d n) p (pairDiagonal (Fin d → ZMod n)) (d * d * (n * n)) ≤ 1 / 4 := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hstoch : IsStochastic (Qcpl d n) := ker_stochastic _
  have ht : 0 < d * d * (n * n) := by positivity
  have hlt := lyapunov_tail (Qcpl d n) hstoch (pairDiagonal (Fin d → ZMod n)) Hfun
    (fun w => Hfun_nonneg w) (1 / (d : ℝ)) (by positivity)
    (fun w hw => Qcpl_drop hd0 hn w hw) p (d * d * (n * n)) ht
  refine le_trans hlt ?_
  have hden : (1 / (d : ℝ)) * ((d * d * (n * n) : ℕ) : ℝ) = (d : ℝ) * (n : ℝ) ^ 2 := by
    push_cast
    field_simp
    try ring
  rw [hden, div_le_div_iff₀ (by positivity) (by norm_num)]
  have hH := Hfun_le p
  nlinarith [hH, hdR, hnR]

end Torus

/-! ## Iterating the contraction -/

section Iterate

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

private lemma tvDist_nonneg (μ ν : V → ℝ) : 0 ≤ tvDist μ ν := by
  have h := le_ciSup (f := fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|)
    (Finite.bddAbove_range _) (∅ : Finset V)
  simpa using h

private lemma distPairs_nonneg (P : Matrix V V ℝ) (t : ℕ) : 0 ≤ distPairs P t := by
  obtain ⟨v⟩ := ‹Nonempty V›
  refine le_trans (tvDist_nonneg (rowDist P t v) (rowDist P t v)) ?_
  exact le_ciSup (f := fun p : V × V => tvDist (rowDist P t p.1) (rowDist P t p.2))
    (Finite.bddAbove_range _) (v, v)

private lemma distPairs_pow (P : Matrix V V ℝ) (hP : IsStochastic P) (t0 : ℕ) (κ : ℝ)
    (h : distPairs P t0 ≤ κ) (m : ℕ) : distPairs P ((m + 1) * t0) ≤ κ ^ (m + 1) := by
  have hκ0 : 0 ≤ κ := le_trans (distPairs_nonneg P t0) h
  induction m with
  | zero => simpa using h
  | succ m ih =>
    have hstep := distPairs_submultiplicative P hP ((m + 1) * t0) t0
    have hre : (m + 1 + 1) * t0 = (m + 1) * t0 + t0 := by ring
    rw [hre]
    refine le_trans hstep ?_
    calc distPairs P ((m + 1) * t0) * distPairs P t0 ≤ κ ^ (m + 1) * κ :=
          mul_le_mul ih h (distPairs_nonneg P t0) (pow_nonneg hκ0 _)
      _ = κ ^ (m + 1 + 1) := by ring

end Iterate

end

end MarkovMixing

open MarkovMixing

open scoped BigOperators

/-- **Theorem 5.5** (LPW): the lazy random walk on the `d`-dimensional torus
`ℤ_n^d` satisfies `t_mix(ε) ≤ c(d) n² log₂(ε⁻¹)` for a constant `c(d)`
depending only on the dimension `d`. -/
theorem solution (d : ℕ) (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) [NeZero n], 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      (mixingTime (lazy (graphWalk (torusGraph d n)))
          (uniformDist (Fin d → ZMod n)) ε : ℝ) ≤
        c * n ^ 2 * Real.logb 2 ε⁻¹ := by
  refine ⟨2 * (d : ℝ) ^ 2, by positivity, ?_⟩
  intro n _inst hn ε hε hε2
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hstoch : IsStochastic (lazy (graphWalk (torusGraph d n))) := by
    rw [lazy_eq_ker hd hn]; exact ker_stochastic _
  have hstat : IsStationary (lazy (graphWalk (torusGraph d n)))
      (uniformDist (Fin d → ZMod n)) := by
    rw [lazy_eq_ker hd hn]; exact ker_uniform_stationary mv mv_bijective
  -- one round of the coupling brings `d̄` down to `1/4`
  have hquarter : distPairs (lazy (graphWalk (torusGraph d n))) (d * d * (n * n)) ≤ 1 / 4 := by
    have hcb := (coupling_bound (lazy (graphWalk (torusGraph d n))) hstoch
      (uniformDist (Fin d → ZMod n)) hstat (fun _ _ => Qcpl d n)
      (fun _ _ => Qcpl_markovian hd hn) (d * d * (n * n))).1
    simp only [distPairs]
    exact ciSup_le fun p => le_trans (hcb p.1 p.2) (tail_quarter hd hn (p.1, p.2))
  -- elementary facts about `L = log₂ (1/ε)`
  have hinvpos : (0 : ℝ) < ε⁻¹ := inv_pos.mpr hε
  have hmul : ε * ε⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hε)
  have hεinv : (2 : ℝ) ≤ ε⁻¹ := by nlinarith [mul_le_mul_of_nonneg_right hε2 hinvpos.le]
  have hL1 : 1 ≤ Real.logb 2 ε⁻¹ := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hinvpos, Real.rpow_one]
    exact hεinv
  have hL0 : (0 : ℝ) ≤ Real.logb 2 ε⁻¹ := le_trans zero_le_one hL1
  have hmge : Real.logb 2 ε⁻¹ ≤ (⌈Real.logb 2 ε⁻¹⌉₊ : ℝ) := Nat.le_ceil _
  have hmlt : (⌈Real.logb 2 ε⁻¹⌉₊ : ℝ) < Real.logb 2 ε⁻¹ + 1 := Nat.ceil_lt_add_one hL0
  have hm1 : 1 ≤ ⌈Real.logb 2 ε⁻¹⌉₊ := by
    rcases Nat.eq_zero_or_pos ⌈Real.logb 2 ε⁻¹⌉₊ with h | h
    · rw [h, Nat.cast_zero] at hmge; linarith
    · exact h
  obtain ⟨m, hmeq⟩ : ∃ m, ⌈Real.logb 2 ε⁻¹⌉₊ = m + 1 := ⟨⌈Real.logb 2 ε⁻¹⌉₊ - 1, by omega⟩
  rw [hmeq] at hmge hmlt
  -- `d̄` decays geometrically
  have hpow := distPairs_pow (lazy (graphWalk (torusGraph d n))) hstoch (d * d * (n * n))
    (1 / 4) hquarter m
  have hεbd : (1 / 4 : ℝ) ^ (m + 1) ≤ ε := by
    have hpos : (0 : ℝ) < 4 ^ (m + 1) := by positivity
    have h4 : ε⁻¹ ≤ 4 ^ (m + 1) := by
      calc ε⁻¹ = (2 : ℝ) ^ (Real.logb 2 ε⁻¹) :=
            (Real.rpow_logb (by norm_num) (by norm_num) hinvpos).symm
        _ ≤ (2 : ℝ) ^ (((m : ℝ) + 1)) :=
            (Real.rpow_le_rpow_left_iff (by norm_num)).mpr (by push_cast at hmge; linarith)
        _ = (2 : ℝ) ^ (m + 1) := by
            rw [show ((m : ℝ) + 1) = (((m + 1 : ℕ) : ℝ)) by push_cast; ring, Real.rpow_natCast]
        _ ≤ (4 : ℝ) ^ (m + 1) := by
            exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have h1 : 1 ≤ ε * 4 ^ (m + 1) := by
      have h2 := mul_le_mul_of_nonneg_left h4 hε.le
      rwa [hmul] at h2
    calc (1 / 4 : ℝ) ^ (m + 1) = 1 / 4 ^ (m + 1) := by rw [div_pow, one_pow]
      _ ≤ ε := by rw [div_le_iff₀ hpos]; linarith
  have hd4 : distStationary (lazy (graphWalk (torusGraph d n)))
      (uniformDist (Fin d → ZMod n)) ((m + 1) * (d * d * (n * n))) ≤ ε :=
    le_trans (dist_le_distPairs (lazy (graphWalk (torusGraph d n))) hstoch
      (uniformDist (Fin d → ZMod n)) hstat _).1 (le_trans hpow hεbd)
  have hmix : mixingTime (lazy (graphWalk (torusGraph d n)))
      (uniformDist (Fin d → ZMod n)) ε ≤ (m + 1) * (d * d * (n * n)) := Nat.sInf_le hd4
  have hcast : ((mixingTime (lazy (graphWalk (torusGraph d n)))
      (uniformDist (Fin d → ZMod n)) ε : ℕ) : ℝ)
      ≤ (((m + 1) * (d * d * (n * n)) : ℕ) : ℝ) := by exact_mod_cast hmix
  refine le_trans hcast ?_
  have hmle : ((m : ℝ) + 1) ≤ 2 * Real.logb 2 ε⁻¹ := by push_cast at hmlt; linarith
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hnn2 : (0 : ℝ) ≤ (d : ℝ) * (d : ℝ) * ((n : ℝ) * (n : ℝ)) := by positivity
  have hkey := mul_le_mul_of_nonneg_right hmle hnn2
  push_cast
  nlinarith [hkey]
