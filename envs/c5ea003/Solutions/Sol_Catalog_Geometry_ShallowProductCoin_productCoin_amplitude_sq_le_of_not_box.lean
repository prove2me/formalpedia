-- Prove2me | solution 1 for Catalog.Geometry.ShallowProductCoin.productCoin_amplitude_sq_le_of_not_box
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:49:12.62495+00:00
-- url     : https://prove2.me/submissions/aa5d39b7-b2b6-4258-86e4-ab32db4ed75a

import Mathlib
import Definitions.Def_Geometry_ShallowProductCoinRigidity

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Geometry/ShallowProductCoinRigidity.lean ====
/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/

/-!
# Rigidity gap for shallow product coins

## Setting

A *resonance set* is a finite set `R` of states inside a finite state space `X`.
A *coin* is a real weight function `psi : X → ℝ` normalised so that `∑ x, psi x ^ 2 = 1`.
Its *resonance amplitude* is

  `A(psi) = ∑ x ∈ R, psi x`.

Cauchy–Schwarz gives `A(psi) ^ 2 ≤ |R|`, with equality exactly for the (normalised)
indicator of `R`.  This file makes that rigidity **quantitative** for the class of
*product coins*, i.e. coins that factor over the coordinates of the state and hence
cannot "see" the global shape of `R`.

## Main results

* `resonanceAmplitude_defect_identity` — the exact identity
  `|R| - A(psi)^2 = |R| * ∑ x, (psi x - (A/|R|) * 1_R x)^2`.
* `resonanceAmplitude_sq_le` — `A(psi)^2 ≤ |R|`.
* `resonanceAmplitude_sq_eq_iff` — equality holds iff `psi` is a scalar multiple of `1_R`.
* `productCoin_amplitude_sq_le_of_not_box` — **depth-2 rigidity gap.**  If `R ⊆ A × B`
  is not a combinatorial box, then *every* unit product coin `f ⊗ g` satisfies
  `A(f ⊗ g)^2 ≤ |R| - 1/(9 |R|)`.
* `productCoin_amplitude_sq_le_mul_of_not_box` — the same in the form
  `A(f ⊗ g)^2 ≤ (1 - c) |R|` with `c = 1/(9|R|^2) > 0`.
* `productCoin_depth_amplitude_sq_le_of_not_box`,
  `productCoin_depth_amplitude_sq_le_mul_of_not_box` — **depth-`n` rigidity gap** with
  the *same* constant `c = 1/(9|R|^2)`, uniform in the depth `n`.

The constant is explicit and depends only on `|R|`; the hypothesis `|R| ≥ 2` is
automatic from the non-box witness (`two_le_card_of_not_box`).

## Proof mechanism

Write `M` for the 0/1 indicator matrix of `R ⊆ A × B` and `t` for the amplitude of a
unit product coin `f ⊗ g`.  Then `E := M - t · f gᵀ` obeys the exact Pythagoras identity
`‖E‖_F^2 = |R| - t^2` (`prod_defect_identity`).  Failure of `R` to be a box produces a
`2 × 2` submatrix of `M` of determinant `1`, while the corresponding `2 × 2` submatrix of
the rank-one matrix `t · f gᵀ` has determinant `0`.  Expanding the determinant of `M`
along `E` and applying the four-term Cauchy–Schwarz inequality forces
`‖E‖_F^2 ≥ 1/(9|R|)` (`rigidity_gap_core`).
-/

namespace Catalog.Geometry.ShallowProductCoin

open Finset

/-! ## 1. Resonance amplitude and the exact Cauchy–Schwarz defect -/

-- [dropped: platform already declares resonanceAmplitude]
-- [dropped: platform already declares IsUnitCoin]
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Exact Cauchy–Schwarz defect identity.**  For a unit coin the gap `|R| - A(psi)^2`
equals `|R|` times the squared `ℓ²`-distance from `psi` to the best scalar multiple of
the indicator of `R`. -/
theorem resonanceAmplitude_defect_identity (R : Finset X) (psi : X → ℝ)
    (hpsi : IsUnitCoin psi) (hR : R.Nonempty) :
    (R.card : ℝ) - resonanceAmplitude R psi ^ 2 =
      R.card * ∑ x, (psi x -
        (resonanceAmplitude R psi / R.card) * (if x ∈ R then (1:ℝ) else 0)) ^ 2 := by
  have hcard : (0:ℝ) < R.card := by exact_mod_cast Finset.card_pos.mpr hR
  set c : ℝ := resonanceAmplitude R psi / R.card with hc
  have hsum : ∑ x, (psi x - c * (if x ∈ R then (1:ℝ) else 0)) ^ 2
      = (∑ x, psi x ^ 2) - 2 * c * (∑ x ∈ R, psi x) + c ^ 2 * R.card := by
    have h1 : ∀ x : X, (psi x - c * (if x ∈ R then (1:ℝ) else 0)) ^ 2
        = psi x ^ 2 - 2 * c * (if x ∈ R then psi x else 0)
          + c ^ 2 * (if x ∈ R then (1:ℝ) else 0) := by
      intro x; by_cases hx : x ∈ R <;> simp [hx]; ring
    simp only [h1]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp [Finset.sum_ite_mem]
  rw [hsum, hpsi]
  have hAmp : (∑ x ∈ R, psi x) = resonanceAmplitude R psi := rfl
  rw [hAmp, hc]
  field_simp
  ring

/-- **Cauchy–Schwarz bound.**  Any unit coin has resonance amplitude squared at most `|R|`. -/
theorem resonanceAmplitude_sq_le (R : Finset X) (psi : X → ℝ) (hpsi : IsUnitCoin psi) :
    resonanceAmplitude R psi ^ 2 ≤ R.card := by
  rcases R.eq_empty_or_nonempty with rfl | hR
  · simp [resonanceAmplitude]
  · have hid := resonanceAmplitude_defect_identity R psi hpsi hR
    have hnn : (0:ℝ) ≤ R.card * ∑ x, (psi x -
        (resonanceAmplitude R psi / R.card) * (if x ∈ R then (1:ℝ) else 0)) ^ 2 :=
      mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    linarith

/-- **Rigidity.**  The Cauchy–Schwarz bound is attained exactly by the scalar multiples of
the indicator function of `R`. -/
theorem resonanceAmplitude_sq_eq_iff (R : Finset X) (psi : X → ℝ)
    (hpsi : IsUnitCoin psi) (hR : R.Nonempty) :
    resonanceAmplitude R psi ^ 2 = R.card ↔
      ∃ c : ℝ, ∀ x, psi x = c * (if x ∈ R then (1:ℝ) else 0) := by
  have hcard : (0:ℝ) < R.card := by exact_mod_cast Finset.card_pos.mpr hR
  have hid := resonanceAmplitude_defect_identity R psi hpsi hR
  constructor
  · intro heq
    refine ⟨resonanceAmplitude R psi / R.card, ?_⟩
    have hzero : ∑ x, (psi x -
        (resonanceAmplitude R psi / R.card) * (if x ∈ R then (1:ℝ) else 0)) ^ 2 = 0 := by
      have hmul : (R.card : ℝ) * ∑ x, (psi x -
          (resonanceAmplitude R psi / R.card) * (if x ∈ R then (1:ℝ) else 0)) ^ 2 = 0 := by
        rw [← hid, heq]; ring
      rcases mul_eq_zero.mp hmul with h | h
      · exact absurd h (ne_of_gt hcard)
      · exact h
    intro x
    have hx0 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (univ : Finset X)) => sq_nonneg _)).mp hzero x (mem_univ x)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx0
    linarith
  · rintro ⟨c, hcf⟩
    have hA : resonanceAmplitude R psi = c * R.card := by
      simp only [resonanceAmplitude, hcf]
      simp [mul_comm]
    have hnorm : (c ^ 2) * R.card = 1 := by
      have hsq : ∑ x, psi x ^ 2 = c ^ 2 * R.card := by
        simp only [hcf]
        have hpt : ∀ x : X, (c * (if x ∈ R then (1:ℝ) else 0)) ^ 2
            = c ^ 2 * (if x ∈ R then (1:ℝ) else 0) := by
          intro x; by_cases hx : x ∈ R <;> simp [hx]
        simp only [hpt, ← Finset.mul_sum]
        simp [mul_comm]
      rw [← hsq]; exact hpsi
    rw [hA]
    nlinarith [hnorm]

/-! ## 2. The algebraic core of the gap

A purely real-algebraic statement: a `2 × 2` integer block of determinant `1` cannot be
approximated too well, in Frobenius norm, by a `2 × 2` block of a rank-one matrix. -/

/-- Four-term Cauchy–Schwarz, in the exact shape needed for the determinant expansion. -/
private lemma four_term_cauchy_schwarz (m1 m2 m3 m4 e1 e2 e3 e4 : ℝ) :
    (m1 * e4 + m4 * e1 - m2 * e3 - m3 * e2) ^ 2
      ≤ (m1 ^ 2 + m2 ^ 2 + m3 ^ 2 + m4 ^ 2) * (e1 ^ 2 + e2 ^ 2 + e3 ^ 2 + e4 ^ 2) := by
  nlinarith [sq_nonneg (m1 * e1 - m4 * e4), sq_nonneg (m1 * e3 + m2 * e4),
    sq_nonneg (m1 * e2 + m3 * e4), sq_nonneg (m4 * e3 + m2 * e1),
    sq_nonneg (m4 * e2 + m3 * e1), sq_nonneg (m2 * e2 - m3 * e3)]

/-- The `2 × 2` determinant of the error block is at most half its Frobenius energy. -/
private lemma cross_term_bound (e1 e2 e3 e4 : ℝ) :
    |e1 * e4 - e2 * e3| ≤ (e1 ^ 2 + e2 ^ 2 + e3 ^ 2 + e4 ^ 2) / 2 := by
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (e1 + e4), sq_nonneg (e2 - e3)]
  · nlinarith [sq_nonneg (e1 - e4), sq_nonneg (e2 + e3)]

/-- **Algebraic core.**  Let `(m1 m2; m3 m4)` be a `2 × 2` block with `m1 = m4 = 1`,
`m2 = 0` and `m3 ≥ 0` (so its determinant is `1`), and let `(x1 x2; x3 x4)` be a singular
block (`x1 x4 = x2 x3`).  If `P` is the squared Frobenius distance between the blocks,
`Msq` the squared Frobenius norm of the first block, `Msq ≤ Rc` and `P ≤ S`, then
`S ≥ 1/(9 Rc)`. -/
private lemma rigidity_gap_core {m1 m2 m3 m4 x1 x2 x3 x4 P Msq S Rc : ℝ}
    (hm1 : m1 = 1) (hm2 : m2 = 0) (hm4 : m4 = 1)
    (hx : x1 * x4 = x2 * x3)
    (hP : P = (m1 - x1) ^ 2 + (m2 - x2) ^ 2 + (m3 - x3) ^ 2 + (m4 - x4) ^ 2)
    (hMsq : Msq = m1 ^ 2 + m2 ^ 2 + m3 ^ 2 + m4 ^ 2)
    (hPS : P ≤ S) (hMsqR : Msq ≤ Rc) (hR2 : (2:ℝ) ≤ Rc) :
    1 / (9 * Rc) ≤ S := by
  -- make the four error entries opaque local constants
  obtain ⟨e1, e2, e3, e4, he1, he2, he3, he4⟩ :
      ∃ e1 e2 e3 e4 : ℝ, e1 = m1 - x1 ∧ e2 = m2 - x2 ∧ e3 = m3 - x3 ∧ e4 = m4 - x4 :=
    ⟨_, _, _, _, rfl, rfl, rfl, rfl⟩
  rw [← he1, ← he2, ← he3, ← he4] at hP
  -- determinant expansion: the rank-one block contributes nothing
  have hdet1 : (m1 * e4 + m4 * e1 - m2 * e3 - m3 * e2) - (e1 * e4 - e2 * e3) = 1 := by
    rw [he1, he2, he3, he4, hm1, hm2, hm4]
    linear_combination -hx
  have hCS : (m1 * e4 + m4 * e1 - m2 * e3 - m3 * e2) ^ 2 ≤ Msq * P := by
    rw [hMsq, hP]; exact four_term_cauchy_schwarz m1 m2 m3 m4 e1 e2 e3 e4
  have hcross : |e1 * e4 - e2 * e3| ≤ P / 2 := by
    rw [hP]; exact cross_term_bound e1 e2 e3 e4
  have hPnn : 0 ≤ P := by rw [hP]; positivity
  have hRcpos : (0:ℝ) < Rc := by linarith
  by_contra hcon
  push_neg at hcon
  have hPlt : P < 1 / (9 * Rc) := lt_of_le_of_lt hPS hcon
  have hbnd : 1 / (9 * Rc) ≤ 1 / 18 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith
  have hPsmall : P < 1 / 18 := lt_of_lt_of_le hPlt hbnd
  have hUlb : (35 : ℝ) / 36 ≤ m1 * e4 + m4 * e1 - m2 * e3 - m3 * e2 := by
    have := abs_le.mp hcross
    linarith [hdet1]
  have hU2 : ((35 : ℝ) / 36) ^ 2 ≤ (m1 * e4 + m4 * e1 - m2 * e3 - m3 * e2) ^ 2 := by
    nlinarith
  have hMP : Msq * P ≤ Rc * P := mul_le_mul_of_nonneg_right hMsqR hPnn
  have hRP : Rc * P < 1 / 9 := by
    have h1 : Rc * P < Rc * (1 / (9 * Rc)) := by nlinarith
    have h2 : Rc * (1 / (9 * Rc)) = 1 / 9 := by field_simp
    linarith [h2 ▸ h1]
  norm_num at hU2
  linarith

/-! ## 3. Depth-2 product coins: the rigidity gap -/

section Depth2

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

-- [dropped: platform already declares IsBox]
theorem isBox_iff_eq_product (R : Finset (A × B)) :
    IsBox R ↔ R = (R.image Prod.fst) ×ˢ (R.image Prod.snd) := by
  constructor
  · intro h
    ext ⟨a, b⟩
    simp only [Finset.mem_product, Finset.mem_image]
    constructor
    · intro hab; exact ⟨⟨(a, b), hab, rfl⟩, ⟨(a, b), hab, rfl⟩⟩
    · rintro ⟨⟨⟨a1, b1⟩, hp, rfl⟩, ⟨⟨a2, b2⟩, hq, rfl⟩⟩
      exact h _ _ _ _ hp hq
  · intro h a a' b b' hab hab'
    rw [h] at hab hab' ⊢
    simp only [Finset.mem_product] at hab hab' ⊢
    exact ⟨hab.1, hab'.2⟩

/-- The product (depth-2) coin built from the factors `f` and `g`. -/
-- [dropped: platform already declares prodCoin]
lemma prodCoin_isUnitCoin {f : A → ℝ} {g : B → ℝ}
    (hf : ∑ a, f a ^ 2 = 1) (hg : ∑ b, g b ^ 2 = 1) : IsUnitCoin (prodCoin f g) := by
  unfold IsUnitCoin prodCoin
  rw [Fintype.sum_prod_type]
  have hin : ∀ a : A, ∑ b : B, (f a * g b) ^ 2 = f a ^ 2 := by
    intro a
    have hpt : ∀ b : B, (f a * g b) ^ 2 = f a ^ 2 * g b ^ 2 := by intro b; ring
    simp only [hpt, ← Finset.mul_sum, hg, mul_one]
  simp only [hin, hf]

/-- Auxiliary: a sum of a nonnegative function over four pairwise distinct points is at
most the total sum. -/
lemma four_point_le_total {Y : Type*} [Fintype Y] [DecidableEq Y] (F : Y → ℝ)
    (hF : ∀ y, 0 ≤ F y) {p q r s : Y}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    F p + F q + F r + F s ≤ ∑ y, F y := by
  have hval : ∑ y ∈ ({p, q, r, s} : Finset Y), F y = F p + F q + F r + F s := by
    rw [Finset.sum_insert (by simp [hpq, hpr, hps]),
        Finset.sum_insert (by simp [hqr, hqs]),
        Finset.sum_insert (by simp [hrs]), Finset.sum_singleton]
    ring
  calc F p + F q + F r + F s = ∑ y ∈ ({p, q, r, s} : Finset Y), F y := hval.symm
    _ ≤ ∑ y, F y :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hF i)

/-- The Pythagoras identity: the squared Frobenius distance from the indicator matrix of
`R` to the rank-one matrix `t · f gᵀ` is exactly `|R| - t^2`, where `t` is the amplitude
of the unit product coin `f ⊗ g`. -/
lemma prod_defect_identity (R : Finset (A × B)) (f : A → ℝ) (g : B → ℝ)
    (hf : ∑ a, f a ^ 2 = 1) (hg : ∑ b, g b ^ 2 = 1) :
    ∑ p : A × B, ((if p ∈ R then (1:ℝ) else 0)
        - resonanceAmplitude R (prodCoin f g) * f p.1 * g p.2) ^ 2
      = (R.card : ℝ) - resonanceAmplitude R (prodCoin f g) ^ 2 := by
  set t := resonanceAmplitude R (prodCoin f g) with ht
  have hexpand : ∀ p : A × B,
      ((if p ∈ R then (1:ℝ) else 0) - t * f p.1 * g p.2) ^ 2
        = (if p ∈ R then (1:ℝ) else 0)
          - 2 * t * (if p ∈ R then f p.1 * g p.2 else 0)
          + t ^ 2 * (f p.1 * g p.2) ^ 2 := by
    intro p
    by_cases hp : p ∈ R <;> simp [hp] <;> ring
  simp only [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : ∑ p : A × B, (if p ∈ R then (1:ℝ) else 0) = (R.card : ℝ) := by
    rw [Finset.sum_ite_mem]; simp
  have h2 : ∑ p : A × B, (if p ∈ R then f p.1 * g p.2 else 0) = t := by
    rw [Finset.sum_ite_mem]
    simp only [Finset.univ_inter]
    rfl
  have h3 : ∑ p : A × B, (f p.1 * g p.2) ^ 2 = 1 := prodCoin_isUnitCoin hf hg
  rw [h1, h2, h3]
  ring

omit [Fintype A] [Fintype B] in
/-- A non-box resonance set has at least two elements. -/
theorem two_le_card_of_not_box {R : Finset (A × B)} (hbox : ¬ IsBox R) : 2 ≤ R.card := by
  unfold IsBox at hbox
  push_neg at hbox
  obtain ⟨a, a', b, b', hab, hab', hmix⟩ := hbox
  have haa : a ≠ a' := by rintro rfl; exact hmix hab'
  have hsub : ({(a, b), (a', b')} : Finset (A × B)) ⊆ R := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption
  have hc := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by simp [Prod.ext_iff, haa]), Finset.card_singleton] at hc

/-- **Main depth-2 theorem: the rigidity gap for shallow product coins.**

If the resonance set `R ⊆ A × B` is *not* a combinatorial box, then no unit product coin
`f ⊗ g` comes within `1/(9|R|)` of the Cauchy–Schwarz optimum `|R|`. -/
theorem productCoin_amplitude_sq_le_of_not_box (R : Finset (A × B))
    (f : A → ℝ) (g : B → ℝ) (hf : ∑ a, f a ^ 2 = 1) (hg : ∑ b, g b ^ 2 = 1)
    (hbox : ¬ IsBox R) :
    resonanceAmplitude R (prodCoin f g) ^ 2 ≤ (R.card : ℝ) - 1 / (9 * R.card) := by
  obtain ⟨a, a', b, b', hab, hab', hmix⟩ :
      ∃ a a' b b', (a, b) ∈ R ∧ (a', b') ∈ R ∧ (a, b') ∉ R := by
    unfold IsBox at hbox
    push_neg at hbox
    obtain ⟨a, a', b, b', h1, h2, h3⟩ := hbox
    exact ⟨a, a', b, b', h1, h2, h3⟩
  have haa : a ≠ a' := by rintro rfl; exact hmix hab'
  have hbb : b ≠ b' := by rintro rfl; exact hmix hab
  have hR2 : (2:ℝ) ≤ (R.card : ℝ) := by exact_mod_cast two_le_card_of_not_box hbox
  set t := resonanceAmplitude R (prodCoin f g) with ht
  set M : A × B → ℝ := fun p => if p ∈ R then (1:ℝ) else 0 with hM
  set E : A × B → ℝ := fun p => M p - t * f p.1 * g p.2 with hE
  have hSid : ∑ p : A × B, E p ^ 2 = (R.card : ℝ) - t ^ 2 :=
    prod_defect_identity R f g hf hg
  -- the four sample points are pairwise distinct
  have d1 : (a, b) ≠ (a, b') := by simp [Prod.ext_iff, hbb]
  have d2 : (a, b) ≠ (a', b) := by simp [Prod.ext_iff, haa]
  have d3 : (a, b) ≠ (a', b') := by simp [Prod.ext_iff, haa]
  have d4 : (a, b') ≠ (a', b) := by simp [Prod.ext_iff, haa]
  have d5 : (a, b') ≠ (a', b') := by simp [Prod.ext_iff, haa]
  have d6 : (a', b) ≠ (a', b') := by simp [Prod.ext_iff, hbb]
  have hm1v : M (a, b) = 1 := by simp [hM, hab]
  have hm2v : M (a, b') = 0 := by simp [hM, hmix]
  have hm4v : M (a', b') = 1 := by simp [hM, hab']
  -- four-point energy is at most total energy
  have hPS : E (a, b) ^ 2 + E (a, b') ^ 2 + E (a', b) ^ 2 + E (a', b') ^ 2
      ≤ (R.card : ℝ) - t ^ 2 := by
    rw [← hSid]
    exact four_point_le_total (fun p => E p ^ 2) (fun _ => sq_nonneg _) d1 d2 d3 d4 d5 d6
  -- four-point matrix mass is at most `|R|`
  have hMtot : ∑ p : A × B, M p ^ 2 = (R.card : ℝ) := by
    have hpt : ∀ p : A × B, M p ^ 2 = if p ∈ R then (1:ℝ) else 0 := by
      intro p; simp only [hM]; by_cases hp : p ∈ R <;> simp [hp]
    simp only [hpt]
    rw [Finset.sum_ite_mem]; simp
  have hMsqR : M (a, b) ^ 2 + M (a, b') ^ 2 + M (a', b) ^ 2 + M (a', b') ^ 2
      ≤ (R.card : ℝ) := by
    rw [← hMtot]
    exact four_point_le_total (fun p => M p ^ 2) (fun _ => sq_nonneg _) d1 d2 d3 d4 d5 d6
  -- rank-one relation for the four sampled entries
  have hx : (t * f a * g b) * (t * f a' * g b') = (t * f a * g b') * (t * f a' * g b) := by
    ring
  have hPeq : E (a, b) ^ 2 + E (a, b') ^ 2 + E (a', b) ^ 2 + E (a', b') ^ 2
      = (M (a, b) - t * f a * g b) ^ 2 + (M (a, b') - t * f a * g b') ^ 2
        + (M (a', b) - t * f a' * g b) ^ 2 + (M (a', b') - t * f a' * g b') ^ 2 := rfl
  have hgap : 1 / (9 * (R.card : ℝ)) ≤ (R.card : ℝ) - t ^ 2 :=
    rigidity_gap_core (m1 := M (a, b)) (m2 := M (a, b')) (m3 := M (a', b))
      (m4 := M (a', b')) (x1 := t * f a * g b) (x2 := t * f a * g b')
      (x3 := t * f a' * g b) (x4 := t * f a' * g b')
      hm1v hm2v hm4v hx hPeq rfl hPS hMsqR hR2
  have hRpos : (0:ℝ) < 9 * (R.card : ℝ) := by linarith
  linarith

/-- Multiplicative form of the depth-2 gap: `A(f ⊗ g)^2 ≤ (1 - c) * |R|` with the
explicit constant `c = 1/(9 |R|^2) > 0`. -/
theorem productCoin_amplitude_sq_le_mul_of_not_box (R : Finset (A × B))
    (f : A → ℝ) (g : B → ℝ) (hf : ∑ a, f a ^ 2 = 1) (hg : ∑ b, g b ^ 2 = 1)
    (hbox : ¬ IsBox R) :
    resonanceAmplitude R (prodCoin f g) ^ 2
      ≤ (1 - 1 / (9 * (R.card : ℝ) ^ 2)) * (R.card : ℝ) := by
  have hmain := productCoin_amplitude_sq_le_of_not_box R f g hf hg hbox
  have hR2 : (2:ℝ) ≤ (R.card : ℝ) := by exact_mod_cast two_le_card_of_not_box hbox
  have heq : (1 - 1 / (9 * (R.card : ℝ) ^ 2)) * (R.card : ℝ)
      = (R.card : ℝ) - 1 / (9 * (R.card : ℝ)) := by
    have hne : (R.card : ℝ) ≠ 0 := by linarith
    field_simp
  linarith [heq ▸ hmain]

omit [Fintype A] [Fintype B] in
/-- The explicit constant is strictly positive. -/
theorem gap_constant_pos (R : Finset (A × B)) (hbox : ¬ IsBox R) :
    0 < 1 / (9 * (R.card : ℝ) ^ 2) := by
  have hR2 : (2:ℝ) ≤ (R.card : ℝ) := by exact_mod_cast two_le_card_of_not_box hbox
  positivity

/-- Contrapositive packaging: a product coin can only attain the Cauchy–Schwarz optimum
when the resonance set is a combinatorial box.  This is the qualitative "Conjecture 3″"
statement at depth 2. -/
theorem isBox_of_productCoin_optimal (R : Finset (A × B))
    (f : A → ℝ) (g : B → ℝ) (hf : ∑ a, f a ^ 2 = 1) (hg : ∑ b, g b ^ 2 = 1)
    (hopt : resonanceAmplitude R (prodCoin f g) ^ 2 = (R.card : ℝ)) : IsBox R := by
  by_contra hbox
  have hmain := productCoin_amplitude_sq_le_of_not_box R f g hf hg hbox
  rw [hopt] at hmain
  have hR2 : (2:ℝ) ≤ (R.card : ℝ) := by exact_mod_cast two_le_card_of_not_box hbox
  have hpos : (0:ℝ) < 1 / (9 * (R.card : ℝ)) := by positivity
  linarith

end Depth2

/-! ## 4. Depth-`n` product coins -/

section DepthN

variable {D : Type*} [Fintype D] [DecidableEq D]

-- [dropped: platform already declares depthCoin]
lemma depthCoin_isUnitCoin {n : ℕ} (f : Fin n → D → ℝ) (hf : ∀ i, ∑ d, f i d ^ 2 = 1) :
    IsUnitCoin (depthCoin f) := by
  unfold IsUnitCoin depthCoin
  have hsplit : ∑ x : Fin n → D, (∏ i, f i (x i)) ^ 2 = ∏ i, ∑ d, (f i d) ^ 2 := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    exact Finset.sum_congr rfl fun x _ => (Finset.prod_pow _ _ _).symm
  rw [hsplit]
  simp [hf]

/-- The state-space splitting `D^(n+1) ≃ D × D^n` peeling off the first coordinate. -/
-- [dropped: platform already declares peel]
@[simp] lemma peel_apply {n : ℕ} (x : Fin (n + 1) → D) :
    peel n x = (x 0, fun i => x i.succ) := rfl

/-- **Main depth-`n` theorem: the rigidity gap for shallow product coins of any depth.**

If the resonance set `R ⊆ D^(n+1)` is not a box with respect to the split of the first
coordinate off the remaining `n`, then every depth-`(n+1)` product coin obeys
`A(psi)^2 ≤ |R| - 1/(9|R|)`.  The constant does **not** degrade with the depth `n`. -/
theorem productCoin_depth_amplitude_sq_le_of_not_box {n : ℕ}
    (R : Finset (Fin (n + 1) → D)) (f : Fin (n + 1) → D → ℝ)
    (hf : ∀ i, ∑ d, f i d ^ 2 = 1)
    (hbox : ¬ IsBox (R.map (peel n).toEmbedding)) :
    resonanceAmplitude R (depthCoin f) ^ 2 ≤ (R.card : ℝ) - 1 / (9 * R.card) := by
  set R' := R.map (peel n).toEmbedding with hR'
  set g : (Fin n → D) → ℝ := depthCoin (fun i => f i.succ) with hg
  have hgu : ∑ z : Fin n → D, g z ^ 2 = 1 :=
    depthCoin_isUnitCoin (fun i => f i.succ) (fun i => hf i.succ)
  have hfu : ∑ d, f 0 d ^ 2 = 1 := hf 0
  have hamp : resonanceAmplitude R' (prodCoin (f 0) g) = resonanceAmplitude R (depthCoin f) := by
    unfold resonanceAmplitude
    rw [hR', Finset.sum_map]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Equiv.coe_toEmbedding, peel_apply, prodCoin, hg, depthCoin]
    rw [Fin.prod_univ_succ]
  have hcard : R'.card = R.card := by rw [hR', Finset.card_map]
  have hmain := productCoin_amplitude_sq_le_of_not_box R' (f 0) g hfu hgu hbox
  rw [hamp, hcard] at hmain
  exact hmain

/-- Multiplicative depth-`n` form: `A(psi)^2 ≤ (1 - c) |R|` with `c = 1/(9|R|^2) > 0`,
independent of the depth. -/
theorem productCoin_depth_amplitude_sq_le_mul_of_not_box {n : ℕ}
    (R : Finset (Fin (n + 1) → D)) (f : Fin (n + 1) → D → ℝ)
    (hf : ∀ i, ∑ d, f i d ^ 2 = 1)
    (hbox : ¬ IsBox (R.map (peel n).toEmbedding)) :
    resonanceAmplitude R (depthCoin f) ^ 2
      ≤ (1 - 1 / (9 * (R.card : ℝ) ^ 2)) * (R.card : ℝ) := by
  have hmain := productCoin_depth_amplitude_sq_le_of_not_box R f hf hbox
  have hR2 : (2:ℝ) ≤ (R.card : ℝ) := by
    have := two_le_card_of_not_box hbox
    rw [Finset.card_map] at this
    exact_mod_cast this
  have heq : (1 - 1 / (9 * (R.card : ℝ) ^ 2)) * (R.card : ℝ)
      = (R.card : ℝ) - 1 / (9 * (R.card : ℝ)) := by
    have hne : (R.card : ℝ) ≠ 0 := by linarith
    field_simp
  linarith [heq ▸ hmain]

end DepthN

end Catalog.Geometry.ShallowProductCoin
section
open Catalog.Geometry.ShallowProductCoin
open Finset
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem solution (R : Finset (A × B))
    (f : A → ℝ) (g : B → ℝ) (hf : ∑ a, f a ^ 2 = 1) (hg : ∑ b, g b ^ 2 = 1)
    (hbox : ¬ IsBox R) :
    resonanceAmplitude R (prodCoin f g) ^ 2 ≤ (R.card : ℝ) - 1 / (9 * R.card) := by
  first
  | exact Catalog.Geometry.ShallowProductCoin.productCoin_amplitude_sq_le_of_not_box R f g hf hg hbox
  | exact Catalog.Geometry.ShallowProductCoin.productCoin_amplitude_sq_le_of_not_box
  | exact @Catalog.Geometry.ShallowProductCoin.productCoin_amplitude_sq_le_of_not_box R f g hf hg hbox
  | apply Catalog.Geometry.ShallowProductCoin.productCoin_amplitude_sq_le_of_not_box
  | exact Catalog.Geometry.ShallowProductCoin.productCoin_amplitude_sq_le_of_not_box ..


end
