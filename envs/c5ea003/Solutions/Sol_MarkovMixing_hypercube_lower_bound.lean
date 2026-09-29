-- Prove2me | solution 1 for MarkovMixing.hypercube_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T20:47:31.137643+00:00
-- url     : https://prove2.me/submissions/09ac7425-355e-4be8-ab91-d54c46769e9e

import Definitions.Def_mm_lower
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_MarkovMixing_distinguishing_statistic_nondegenerate

/-!
# Lower bound for the lazy hypercube walk (LPW Proposition 7.13)
-/

namespace MarkovMixing

noncomputable section
open scoped BigOperators
open Finset

variable {n : ℕ}

private lemma z2_ff : ∀ a : ZMod 2, a + 1 + 1 = a := by decide
private lemma z2_sub : ∀ a : ZMod 2, a - 1 = a + 1 := by decide
private lemma z2_ne : ∀ a : ZMod 2, a + 1 ≠ a := by decide

/-- Flip the `j`-th coordinate of a hypercube configuration. -/
private def flp (x : Fin n → ZMod 2) (j : Fin n) : Fin n → ZMod 2 :=
  Function.update x j (x j + 1)

private lemma flp_self (x : Fin n → ZMod 2) (j : Fin n) : flp x j j = x j + 1 := by
  simp [flp]

private lemma flp_ne {x : Fin n → ZMod 2} {i j : Fin n} (h : i ≠ j) :
    flp x j i = x i := by
  simp [flp, Function.update_of_ne h]

private lemma flp_invol (x : Fin n → ZMod 2) (j : Fin n) : flp (flp x j) j = x := by
  funext i
  by_cases h : i = j
  · subst h; rw [flp_self, flp_self, z2_ff]
  · rw [flp_ne h, flp_ne h]

private lemma flp_neq (x : Fin n → ZMod 2) (j : Fin n) : flp x j ≠ x := by
  intro h
  exact z2_ne (x j) ((flp_self x j) ▸ congrFun h j)

private lemma flp_inj (x : Fin n → ZMod 2) : Function.Injective (flp x) := by
  intro i j hij
  by_contra hne
  have h1 := congrFun hij i
  rw [flp_self, flp_ne hne] at h1
  exact z2_ne (x i) h1

/-- Adjacency in the hypercube is exactly a single coordinate flip. -/
private lemma adj_iff (x y : Fin n → ZMod 2) :
    (torusGraph n 2).Adj x y ↔ ∃ j : Fin n, y = flp x j := by
  constructor
  · rintro ⟨-, j, hoff, hj⟩
    refine ⟨j, funext fun i => ?_⟩
    by_cases h : i = j
    · subst h
      rw [flp_self]
      rcases hj with h | h
      · exact h
      · rw [h, z2_sub]
    · rw [flp_ne h]; exact (hoff i h).symm
  · rintro ⟨j, rfl⟩
    refine ⟨(flp_neq x j).symm, j, ?_, ?_⟩
    · intro i hi; exact (flp_ne hi).symm
    · exact Or.inl (flp_self x j)

private lemma neighborFinset_eq (x : Fin n → ZMod 2) :
    (torusGraph n 2).neighborFinset x = Finset.univ.image (flp x) := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image, Finset.mem_univ,
    true_and, adj_iff]
  exact ⟨fun ⟨j, hj⟩ => ⟨j, hj.symm⟩, fun ⟨j, hj⟩ => ⟨j, hj.symm⟩⟩

private lemma degree_eq (x : Fin n → ZMod 2) : (torusGraph n 2).degree x = n := by
  rw [SimpleGraph.degree, neighborFinset_eq,
    Finset.card_image_of_injective _ (flp_inj x), Finset.card_univ, Fintype.card_fin]

private lemma sum_graphWalk (x : Fin n → ZMod 2) (f : (Fin n → ZMod 2) → ℝ) :
    ∑ y, graphWalk (torusGraph n 2) x y * f y
      = (n : ℝ)⁻¹ * ∑ j : Fin n, f (flp x j) := by
  classical
  have h1 : ∑ y, graphWalk (torusGraph n 2) x y * f y
      = ∑ y ∈ Finset.univ.filter fun y => (torusGraph n 2).Adj x y,
          ((n : ℝ))⁻¹ * f y := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [graphWalk, degree_eq]
    by_cases h : (torusGraph n 2).Adj x y <;> simp [h]
  have h2 : (Finset.univ.filter fun y => (torusGraph n 2).Adj x y)
      = Finset.univ.image (flp x) := by
    rw [← neighborFinset_eq]
    ext y
    simp [SimpleGraph.mem_neighborFinset]
  rw [h1, h2, Finset.sum_image (fun a _ b _ h => flp_inj x h), Finset.mul_sum]

private lemma sum_lazy (x : Fin n → ZMod 2) (f : (Fin n → ZMod 2) → ℝ) :
    ∑ y, hypercubeWalk n x y * f y
      = 2⁻¹ * f x + 2⁻¹ * ((n : ℝ)⁻¹ * ∑ j : Fin n, f (flp x j)) := by
  classical
  have hentry : ∀ y, hypercubeWalk n x y
      = 2⁻¹ * (if x = y then (1 : ℝ) else 0) + 2⁻¹ * graphWalk (torusGraph n 2) x y := by
    intro y
    simp [hypercubeWalk, lazy, Matrix.one_apply]
  have : ∑ y, hypercubeWalk n x y * f y
      = (∑ y, 2⁻¹ * (if x = y then (1 : ℝ) else 0) * f y)
        + ∑ y, 2⁻¹ * (graphWalk (torusGraph n 2) x y * f y) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by rw [hentry y]; ring
  rw [this, ← Finset.mul_sum, sum_graphWalk]
  congr 1
  rw [Finset.sum_eq_single x]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- The `±1`-valued character of a bit. -/
private def chi (b : ZMod 2) : ℝ := if b = 0 then 1 else -1

private lemma z2_cases : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide

private lemma chi_zero : chi (0 : ZMod 2) = 1 := by simp [chi]

private lemma chi_one : chi (1 : ZMod 2) = -1 := by
  have h : ¬((1 : ZMod 2) = 0) := by decide
  simp [chi, h]

private lemma chi_flip (b : ZMod 2) : chi (b + 1) = -chi b := by
  by_cases h : b = 0
  · subst h
    rw [show ((0 : ZMod 2) + 1) = 1 from rfl, chi_one, chi_zero]
  · rw [z2_cases b h, show ((1 : ZMod 2) + 1) = 0 from rfl, chi_zero, chi_one]
    norm_num

private lemma chi_sq (b : ZMod 2) : chi b * chi b = 1 := by
  by_cases h : b = 0
  · subst h; rw [chi_zero]; norm_num
  · rw [z2_cases b h, chi_one]; norm_num

/-- The Fourier character `χ_S(x) = ∏_{j ∈ S} (−1)^{x_j}`. -/
private def charFn (S : Finset (Fin n)) (x : Fin n → ZMod 2) : ℝ :=
  ∏ j ∈ S, chi (x j)

private lemma charFn_flip (S : Finset (Fin n)) (x : Fin n → ZMod 2) (j : Fin n) :
    charFn S (flp x j) = if j ∈ S then -(charFn S x) else charFn S x := by
  by_cases hj : j ∈ S
  · rw [if_pos hj]
    simp only [charFn]
    rw [← Finset.mul_prod_erase S (fun i => chi (flp x j i)) hj,
      ← Finset.mul_prod_erase S (fun i => chi (x i)) hj, flp_self, chi_flip]
    have hrest : ∏ i ∈ S.erase j, chi (flp x j i) = ∏ i ∈ S.erase j, chi (x i) :=
      Finset.prod_congr rfl fun i hi => by rw [flp_ne (Finset.ne_of_mem_erase hi)]
    rw [hrest]; ring
  · rw [if_neg hj]
    simp only [charFn]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hij : i ≠ j := by
      intro h; exact hj (h ▸ hi)
    rw [flp_ne hij]

private lemma hyper_eigen (hn : 0 < n) (S : Finset (Fin n)) (x : Fin n → ZMod 2) :
    ∑ y, hypercubeWalk n x y * charFn S y
      = (1 - (S.card : ℝ) / n) * charFn S x := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcard : ((n - S.card : ℕ) : ℝ) = (n : ℝ) - S.card := by
    have hle : S.card ≤ n := by
      simpa [Fintype.card_fin] using (Finset.card_le_univ S)
    rw [Nat.cast_sub hle]
  have hsum : ∑ j : Fin n, charFn S (flp x j)
      = ((n : ℝ) - 2 * S.card) * charFn S x := by
    rw [Finset.sum_congr rfl fun j _ => charFn_flip S x j, Finset.sum_ite]
    have hf1 : (Finset.univ.filter fun j : Fin n => j ∈ S) = S := by ext j; simp
    have hf2 : (Finset.univ.filter fun j : Fin n => j ∉ S) = Sᶜ := by ext j; simp
    rw [hf1, hf2, Finset.sum_const, Finset.sum_const, Finset.card_compl,
      Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul, hcard]
    ring
  rw [sum_lazy, hsum]
  field_simp
  ring

private lemma pow_eigen (hn : 0 < n) (S : Finset (Fin n)) (t : ℕ)
    (x : Fin n → ZMod 2) :
    ∑ y, ((hypercubeWalk n) ^ t) x y * charFn S y
      = (1 - (S.card : ℝ) / n) ^ t * charFn S x := by
  induction t generalizing x with
  | zero =>
      simp only [pow_zero, Matrix.one_apply, one_mul]
      rw [Finset.sum_eq_single x]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_univ x) h
  | succ k ih =>
      have hstep : ∀ y, ((hypercubeWalk n) ^ (k + 1)) x y
          = ∑ z, hypercubeWalk n x z * ((hypercubeWalk n) ^ k) z y := by
        intro y; rw [pow_succ']; exact Matrix.mul_apply
      have hexp : ∑ y, ((hypercubeWalk n) ^ (k + 1)) x y * charFn S y
          = ∑ y, ∑ z, hypercubeWalk n x z * ((hypercubeWalk n) ^ k) z y
              * charFn S y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hstep y, Finset.sum_mul]
      rw [hexp, Finset.sum_comm]
      have h2 : ∀ z : Fin n → ZMod 2,
          (∑ y, hypercubeWalk n x z * ((hypercubeWalk n) ^ k) z y * charFn S y)
            = hypercubeWalk n x z * ((1 - (S.card : ℝ) / n) ^ k * charFn S z) := by
        intro z
        have hz : (∑ y, hypercubeWalk n x z * ((hypercubeWalk n) ^ k) z y * charFn S y)
            = hypercubeWalk n x z * ∑ y, ((hypercubeWalk n) ^ k) z y * charFn S y := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
        rw [hz, ih z]
      rw [Finset.sum_congr rfl fun z _ => h2 z]
      have h3 : (∑ z, hypercubeWalk n x z * ((1 - (S.card : ℝ) / n) ^ k * charFn S z))
          = (1 - (S.card : ℝ) / n) ^ k * ∑ z, hypercubeWalk n x z * charFn S z := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
      rw [h3, hyper_eigen hn S x, pow_succ]
      ring

private lemma sum_charFn_zero (S : Finset (Fin n)) (hS : S.Nonempty) :
    ∑ x : Fin n → ZMod 2, charFn S x = 0 := by
  obtain ⟨j, hj⟩ := hS
  let e : (Fin n → ZMod 2) ≃ (Fin n → ZMod 2) :=
    { toFun := fun x => flp x j
      invFun := fun x => flp x j
      left_inv := fun x => flp_invol x j
      right_inv := fun x => flp_invol x j }
  have h1 : ∑ x : Fin n → ZMod 2, charFn S (e x) = ∑ x, charFn S x :=
    Equiv.sum_comp e _
  have h2 : ∑ x : Fin n → ZMod 2, charFn S (e x) = -∑ x, charFn S x := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have := charFn_flip S x j
    rw [if_pos hj] at this
    exact this
  linarith [h1, h2]

private lemma hyper_stochastic (hn : 0 < n) : IsStochastic (hypercubeWalk n) := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  constructor
  · intro x y
    have hentry : hypercubeWalk n x y
        = 2⁻¹ * (if x = y then (1 : ℝ) else 0)
          + 2⁻¹ * graphWalk (torusGraph n 2) x y := by
      simp [hypercubeWalk, lazy, Matrix.one_apply]
    rw [hentry]
    have h1 : (0 : ℝ) ≤ (if x = y then (1 : ℝ) else 0) := by
      by_cases h : x = y <;> simp [h]
    have h2 : (0 : ℝ) ≤ graphWalk (torusGraph n 2) x y := by
      simp only [graphWalk]
      by_cases h : (torusGraph n 2).Adj x y
      · rw [if_pos h]; positivity
      · rw [if_neg h]
    positivity
  · intro x
    have := sum_lazy x (fun _ => (1 : ℝ))
    simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at this
    rw [this]
    field_simp
    norm_num

private lemma pow_stochastic (hn : 0 < n) (t : ℕ) :
    IsStochastic ((hypercubeWalk n) ^ t) := by
  induction t with
  | zero =>
      refine ⟨fun x y => ?_, fun x => ?_⟩
      · simp only [pow_zero, Matrix.one_apply]
        by_cases h : x = y <;> simp [h]
      · simp only [pow_zero, Matrix.one_apply]
        rw [Finset.sum_eq_single x]
        · simp
        · intro b _ hb; simp [Ne.symm hb]
        · intro h; exact absurd (Finset.mem_univ x) h
  | succ k ih =>
      have hP := hyper_stochastic hn
      refine ⟨fun x y => ?_, fun x => ?_⟩
      · rw [pow_succ', Matrix.mul_apply]
        exact Finset.sum_nonneg fun z _ => mul_nonneg (hP.1 x z) (ih.1 z y)
      · have hrow : ∀ y, ((hypercubeWalk n) ^ (k + 1)) x y
            = ∑ z, hypercubeWalk n x z * ((hypercubeWalk n) ^ k) z y := by
          intro y; rw [pow_succ']; exact Matrix.mul_apply
        rw [Finset.sum_congr rfl fun y _ => hrow y, Finset.sum_comm]
        rw [Finset.sum_congr rfl fun z (_ : z ∈ Finset.univ) =>
          (by rw [← Finset.mul_sum, ih.2 z, mul_one] :
            (∑ y, hypercubeWalk n x z * ((hypercubeWalk n) ^ k) z y)
              = hypercubeWalk n x z)]
        exact hP.2 x

private lemma rowDist_isDist (hn : 0 < n) (t : ℕ) (x : Fin n → ZMod 2) :
    IsDist (rowDist (hypercubeWalk n) t x) :=
  ⟨fun y => (pow_stochastic hn t).1 x y, (pow_stochastic hn t).2 x⟩

private lemma uniform_isDist : IsDist (uniformDist (Fin n → ZMod 2)) := by
  have hcard : (0 : ℝ) < (Fintype.card (Fin n → ZMod 2) : ℝ) := by
    have := Fintype.card_pos (α := Fin n → ZMod 2)
    exact_mod_cast this
  refine ⟨fun x => by simp only [uniformDist]; positivity, ?_⟩
  simp only [uniformDist, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- The distinguishing statistic `W(x) = ∑_j (−1)^{x_j}`. -/
private def Wst (n : ℕ) (x : Fin n → ZMod 2) : ℝ := ∑ j : Fin n, chi (x j)

private lemma Wst_eq (x : Fin n → ZMod 2) :
    Wst n x = ∑ j : Fin n, charFn {j} x := by
  simp [Wst, charFn]

private lemma charFn_zero (S : Finset (Fin n)) :
    charFn S (fun _ => (0 : ZMod 2)) = 1 := by
  simp [charFn, chi_zero]

private lemma exp_char_row (hn : 0 < n) (t : ℕ) (S : Finset (Fin n)) :
    ∑ y, charFn S y * rowDist (hypercubeWalk n) t (fun _ => (0 : ZMod 2)) y
      = (1 - (S.card : ℝ) / n) ^ t := by
  have h := pow_eigen hn S t (fun _ => (0 : ZMod 2))
  rw [charFn_zero, mul_one] at h
  rw [← h]
  exact Finset.sum_congr rfl fun y _ => mul_comm _ _

private lemma exp_char_unif (S : Finset (Fin n)) (hS : S.Nonempty) :
    ∑ y : Fin n → ZMod 2, charFn S y * uniformDist (Fin n → ZMod 2) y = 0 := by
  simp only [uniformDist]
  rw [← Finset.sum_mul, sum_charFn_zero S hS, zero_mul]

private lemma var_eq (μ : (Fin n → ZMod 2) → ℝ) (hμ : IsDist μ)
    (f : (Fin n → ZMod 2) → ℝ) :
    distVar μ f = (∑ x, f x * f x * μ x) - (distExp μ f) ^ 2 := by
  simp only [distVar, distExp]
  have hx : ∀ x, (f x - ∑ z, f z * μ z) ^ 2 * μ x
      = (f x * f x * μ x
          - (2 * (∑ z, f z * μ z)) * (f x * μ x))
        + (∑ z, f z * μ z) ^ 2 * μ x := fun x => by ring
  rw [Finset.sum_congr rfl fun x _ => hx x, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hμ.2, mul_one]
  ring

private lemma Wst_sq (x : Fin n → ZMod 2) :
    Wst n x * Wst n x
      = (n : ℝ) + ∑ j : Fin n, ∑ k ∈ Finset.univ.erase j, charFn {j, k} x := by
  simp only [Wst]
  rw [Finset.sum_mul_sum]
  have hj : ∀ j : Fin n, (∑ k : Fin n, chi (x j) * chi (x k))
      = 1 + ∑ k ∈ Finset.univ.erase j, charFn {j, k} x := by
    intro j
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    congr 1
    · exact chi_sq (x j)
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hjk : j ≠ k := Ne.symm (Finset.ne_of_mem_erase hk)
      rw [charFn, Finset.prod_pair hjk]
  rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_add_distrib]
  simp

private lemma second_moment (hn : 0 < n) (μ : (Fin n → ZMod 2) → ℝ) (hμ : IsDist μ)
    (c : ℝ)
    (hc : ∀ j k : Fin n, j ≠ k →
      ∑ y, charFn ({j, k} : Finset (Fin n)) y * μ y = c) :
    ∑ y, Wst n y * Wst n y * μ y = (n : ℝ) + ((n : ℝ) * ((n : ℝ) - 1)) * c := by
  have hexp : ∀ y, Wst n y * Wst n y * μ y
      = (n : ℝ) * μ y
        + ∑ j : Fin n, ∑ k ∈ Finset.univ.erase j, charFn {j, k} y * μ y := by
    intro y
    rw [Wst_sq y, add_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun j _ => Finset.sum_mul _ _ _
  rw [Finset.sum_congr rfl fun y _ => hexp y, Finset.sum_add_distrib,
    ← Finset.mul_sum, hμ.2, mul_one]
  congr 1
  rw [Finset.sum_comm]
  have hinner : ∀ j : Fin n,
      (∑ y, ∑ k ∈ Finset.univ.erase j, charFn ({j, k} : Finset (Fin n)) y * μ y)
        = ((n : ℝ) - 1) * c := by
    intro j
    rw [Finset.sum_comm]
    have : ∀ k ∈ Finset.univ.erase j,
        (∑ y, charFn ({j, k} : Finset (Fin n)) y * μ y) = c := by
      intro k hk
      exact hc j k (Ne.symm (Finset.ne_of_mem_erase hk))
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_erase_of_mem
      (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1
    have : (1 : ℕ) ≤ n := hn
    rw [Nat.cast_sub this, Nat.cast_one]
  rw [Finset.sum_congr rfl fun j _ => hinner j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

private lemma exp_row_W (hn : 0 < n) (t : ℕ) :
    distExp (rowDist (hypercubeWalk n) t (fun _ => (0 : ZMod 2))) (Wst n)
      = (n : ℝ) * (1 - 1 / (n : ℝ)) ^ t := by
  simp only [distExp]
  have h1 : ∀ y, Wst n y * rowDist (hypercubeWalk n) t (fun _ => (0 : ZMod 2)) y
      = ∑ j : Fin n,
          charFn {j} y * rowDist (hypercubeWalk n) t (fun _ => (0 : ZMod 2)) y := by
    intro y; rw [Wst_eq, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun y _ => h1 y, Finset.sum_comm]
  have h2 : ∀ j : Fin n,
      (∑ y, charFn ({j} : Finset (Fin n)) y *
        rowDist (hypercubeWalk n) t (fun _ => (0 : ZMod 2)) y)
        = (1 - 1 / (n : ℝ)) ^ t := by
    intro j
    rw [exp_char_row hn t {j}, Finset.card_singleton]
    norm_num
  rw [Finset.sum_congr rfl fun j _ => h2 j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

private lemma exp_unif_W : distExp (uniformDist (Fin n → ZMod 2)) (Wst n) = 0 := by
  simp only [distExp]
  have h1 : ∀ y, Wst n y * uniformDist (Fin n → ZMod 2) y
      = ∑ j : Fin n, charFn {j} y * uniformDist (Fin n → ZMod 2) y := by
    intro y; rw [Wst_eq, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun y _ => h1 y, Finset.sum_comm]
  have h2 : ∀ j : Fin n,
      (∑ y, charFn ({j} : Finset (Fin n)) y * uniformDist (Fin n → ZMod 2) y) = 0 :=
    fun j => exp_char_unif {j} ⟨j, by simp⟩
  rw [Finset.sum_congr rfl fun j _ => h2 j]
  simp

private lemma var_row_W (hn : 0 < n) (t : ℕ) :
    distVar (rowDist (hypercubeWalk n) t (fun _ => (0 : ZMod 2))) (Wst n)
      = ((n : ℝ) + ((n : ℝ) * ((n : ℝ) - 1)) * (1 - 2 / (n : ℝ)) ^ t)
        - ((n : ℝ) * (1 - 1 / (n : ℝ)) ^ t) ^ 2 := by
  rw [var_eq _ (rowDist_isDist hn t _) _, exp_row_W hn t]
  congr 1
  refine second_moment hn _ (rowDist_isDist hn t _) _ ?_
  intro j k hjk
  rw [exp_char_row hn t {j, k}, Finset.card_pair hjk]
  norm_num

private lemma var_unif_W (hn : 0 < n) :
    distVar (uniformDist (Fin n → ZMod 2)) (Wst n) = (n : ℝ) := by
  rw [var_eq _ uniform_isDist _, exp_unif_W]
  have h := second_moment hn (uniformDist (Fin n → ZMod 2)) uniform_isDist 0
    (fun j k hjk => exp_char_unif {j, k} ⟨j, by simp⟩)
  rw [h]
  ring

private lemma distVar_nonneg (μ : (Fin n → ZMod 2) → ℝ) (hμ : IsDist μ)
    (f : (Fin n → ZMod 2) → ℝ) : 0 ≤ distVar μ f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (sq_nonneg _) (hμ.1 x)

end

end MarkovMixing

open MarkovMixing

/-- **Proposition 7.13** (LPW): lower bound for the lazy hypercube walk. -/
theorem solution (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα : 0 < α)
    (t : ℕ) (ht : (t : ℝ) ≤ 2⁻¹ * n * Real.log n - α * n) :
    1 - 8 * Real.exp (1 - 2 * α) ≤
      distStationary (hypercubeWalk n) (uniformDist (Fin n → ZMod 2)) t := by
  classical
  have hn0 : 0 < n := by omega
  have hN2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hNpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hNm1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hl1pos : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    rw [sub_pos, div_lt_one hNpos]; linarith
  have hl2nn : (0 : ℝ) ≤ 1 - 2 / (n : ℝ) := by
    rw [sub_nonneg, div_le_one hNpos]; linarith
  have hl2le : (1 - 2 / (n : ℝ)) ≤ (1 - 1 / (n : ℝ)) ^ 2 := by
    have hsq : (1 - 1 / (n : ℝ)) ^ 2 = 1 - 2 / (n : ℝ) + (1 / (n : ℝ)) ^ 2 := by
      field_simp; ring
    nlinarith [sq_nonneg (1 / (n : ℝ))]
  have hl1pt : (0 : ℝ) < (1 - 1 / (n : ℝ)) ^ t := pow_pos hl1pos t
  have hpowle : (1 - 2 / (n : ℝ)) ^ t ≤ ((1 - 1 / (n : ℝ)) ^ 2) ^ t :=
    pow_le_pow_left₀ hl2nn hl2le t
  -- the variance of `W` under the row is at most `n`
  have hvar : distVar (rowDist (hypercubeWalk n) t (fun _ => (0 : ZMod 2))) (Wst n)
      ≤ (n : ℝ) := by
    rw [var_row_W hn0 t]
    have h2 : ((n : ℝ) * (1 - 1 / (n : ℝ)) ^ t) ^ 2
        = (n : ℝ) ^ 2 * ((1 - 1 / (n : ℝ)) ^ 2) ^ t := by
      rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
    have h3 : ((n : ℝ) * ((n : ℝ) - 1)) ≤ (n : ℝ) ^ 2 := by nlinarith
    have h4 : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    have h1 : ((n : ℝ) * ((n : ℝ) - 1)) * (1 - 2 / (n : ℝ)) ^ t
        ≤ ((n : ℝ) * (1 - 1 / (n : ℝ)) ^ t) ^ 2 := by
      rw [h2]
      calc ((n : ℝ) * ((n : ℝ) - 1)) * (1 - 2 / (n : ℝ)) ^ t
          ≤ ((n : ℝ) * ((n : ℝ) - 1)) * ((1 - 1 / (n : ℝ)) ^ 2) ^ t :=
            mul_le_mul_of_nonneg_left hpowle h4
        _ ≤ (n : ℝ) ^ 2 * ((1 - 1 / (n : ℝ)) ^ 2) ^ t :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
    linarith
  have hvaru : distVar (uniformDist (Fin n → ZMod 2)) (Wst n) = (n : ℝ) :=
    var_unif_W hn0
  have hsig : (distVar (rowDist (hypercubeWalk n) t (fun _ => (0 : ZMod 2))) (Wst n)
      + distVar (uniformDist (Fin n → ZMod 2)) (Wst n)) / 2 ≤ (n : ℝ) := by
    rw [hvaru]; linarith
  -- the number of standard deviations
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = Real.sqrt (n : ℝ) * (1 - 1 / (n : ℝ)) ^ t :=
    ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by
    rw [hrdef]; exact mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hl1pt)
  have hgap : |distExp (rowDist (hypercubeWalk n) t (fun _ => (0 : ZMod 2))) (Wst n)
      - distExp (uniformDist (Fin n → ZMod 2)) (Wst n)|
      = (n : ℝ) * (1 - 1 / (n : ℝ)) ^ t := by
    rw [exp_row_W hn0 t, exp_unif_W, sub_zero,
      abs_of_pos (mul_pos hNpos hl1pt)]
  have hss : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt (le_of_lt hNpos)
  have hhyp : r * Real.sqrt ((distVar (rowDist (hypercubeWalk n) t
        (fun _ => (0 : ZMod 2))) (Wst n)
      + distVar (uniformDist (Fin n → ZMod 2)) (Wst n)) / 2)
      ≤ |distExp (rowDist (hypercubeWalk n) t (fun _ => (0 : ZMod 2))) (Wst n)
        - distExp (uniformDist (Fin n → ZMod 2)) (Wst n)| := by
    rw [hgap]
    calc r * Real.sqrt ((distVar (rowDist (hypercubeWalk n) t
          (fun _ => (0 : ZMod 2))) (Wst n)
        + distVar (uniformDist (Fin n → ZMod 2)) (Wst n)) / 2)
        ≤ r * Real.sqrt (n : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsig) hr0
      _ = (n : ℝ) * (1 - 1 / (n : ℝ)) ^ t := by
          rw [hrdef]
          calc Real.sqrt (n : ℝ) * (1 - 1 / (n : ℝ)) ^ t * Real.sqrt (n : ℝ)
              = (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) * (1 - 1 / (n : ℝ)) ^ t := by
                ring
            _ = (n : ℝ) * (1 - 1 / (n : ℝ)) ^ t := by rw [hss]
  have hmean : distExp (rowDist (hypercubeWalk n) t (fun _ => (0 : ZMod 2))) (Wst n)
      ≠ distExp (uniformDist (Fin n → ZMod 2)) (Wst n) := by
    rw [exp_row_W hn0 t, exp_unif_W]
    exact ne_of_gt (mul_pos hNpos hl1pt)
  have hprop := distinguishing_statistic_nondegenerate
    (rowDist (hypercubeWalk n) t (fun _ => (0 : ZMod 2)))
    (uniformDist (Fin n → ZMod 2))
    (rowDist_isDist hn0 t _) uniform_isDist (Wst n) hmean r hr0 hhyp
  have hle : tvDist (rowDist (hypercubeWalk n) t (fun _ => (0 : ZMod 2)))
      (uniformDist (Fin n → ZMod 2))
      ≤ distStationary (hypercubeWalk n) (uniformDist (Fin n → ZMod 2)) t := by
    simp only [distStationary]
    have hbdd : BddAbove (Set.range fun x : Fin n → ZMod 2 =>
        tvDist (rowDist (hypercubeWalk n) t x) (uniformDist (Fin n → ZMod 2))) :=
      Set.Finite.bddAbove (Set.finite_range _)
    exact le_ciSup hbdd (fun _ => (0 : ZMod 2))
  -- the analytic estimate
  have hr2 : r ^ 2 = (n : ℝ) * ((1 - 1 / (n : ℝ)) ^ t) ^ 2 := by
    rw [hrdef, mul_pow, Real.sq_sqrt (le_of_lt hNpos)]
  have hr2pos : (0 : ℝ) < r ^ 2 := by
    rw [hr2]; exact mul_pos hNpos (pow_pos hl1pt 2)
  have hlogl1 : -(1 / ((n : ℝ) - 1)) ≤ Real.log (1 - 1 / (n : ℝ)) := by
    have hu : (0 : ℝ) < (n : ℝ) / ((n : ℝ) - 1) := div_pos hNpos hNm1
    have h1 : Real.log ((n : ℝ) / ((n : ℝ) - 1)) ≤ (n : ℝ) / ((n : ℝ) - 1) - 1 :=
      Real.log_le_sub_one_of_pos hu
    have h2 : (n : ℝ) / ((n : ℝ) - 1) - 1 = 1 / ((n : ℝ) - 1) := by
      field_simp
      ring
    have h3 : (1 - 1 / (n : ℝ)) = ((n : ℝ) / ((n : ℝ) - 1))⁻¹ := by
      field_simp
    rw [h3, Real.log_inv]
    linarith
  have hlogn : Real.log (n : ℝ) ≤ (n : ℝ) - 1 := Real.log_le_sub_one_of_pos hNpos
  have hLam : -1 ≤ Real.log (1 - 1 / (n : ℝ)) * ((n : ℝ) - 1) := by
    have hmul := mul_le_mul_of_nonneg_right hlogl1 (le_of_lt hNm1)
    have hh : -(1 / ((n : ℝ) - 1)) * ((n : ℝ) - 1) = -1 := by field_simp
    rw [hh] at hmul
    exact hmul
  have hT0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have h2T : 2 * (t : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) - 2 * α * (n : ℝ) := by
    linarith
  have hkeymul : (2 * α - 1) * ((n : ℝ) - 1)
      ≤ (Real.log (n : ℝ) + 2 * (t : ℝ) * Real.log (1 - 1 / (n : ℝ)))
        * ((n : ℝ) - 1) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (t : ℝ))
      (by linarith : (0 : ℝ) ≤ Real.log (1 - 1 / (n : ℝ)) * ((n : ℝ) - 1) + 1),
      hlogn, hα, h2T]
  have hkey : 2 * α - 1
      ≤ Real.log (n : ℝ) + 2 * (t : ℝ) * Real.log (1 - 1 / (n : ℝ)) :=
    le_of_mul_le_mul_right hkeymul hNm1
  have hlogr2 : Real.log (r ^ 2)
      = Real.log (n : ℝ) + 2 * (t : ℝ) * Real.log (1 - 1 / (n : ℝ)) := by
    rw [hr2, Real.log_mul (ne_of_gt hNpos) (ne_of_gt (pow_pos hl1pt 2)),
      ← pow_mul, Real.log_pow]
    push_cast
    ring
  have hexpr : Real.exp (2 * α - 1) ≤ r ^ 2 := by
    calc Real.exp (2 * α - 1) ≤ Real.exp (Real.log (r ^ 2)) := by
          rw [hlogr2]; exact Real.exp_le_exp.mpr hkey
      _ = r ^ 2 := Real.exp_log hr2pos
  have he : Real.exp (1 - 2 * α) = (Real.exp (2 * α - 1))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  have hfinal : 4 / (4 + r ^ 2) ≤ 8 * Real.exp (1 - 2 * α) := by
    have h1 : (4 : ℝ) / (4 + r ^ 2) ≤ 4 / r ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) hr2pos (by linarith)
    have h2 : (4 : ℝ) / r ^ 2 ≤ 4 / Real.exp (2 * α - 1) :=
      div_le_div_of_nonneg_left (by norm_num) (Real.exp_pos _) hexpr
    have h3 : (4 : ℝ) / Real.exp (2 * α - 1) = 4 * Real.exp (1 - 2 * α) := by
      rw [he, div_eq_mul_inv]
    have h4 : (0 : ℝ) < Real.exp (1 - 2 * α) := Real.exp_pos _
    linarith
  linarith [hprop, hle, hfinal]
