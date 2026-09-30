-- Prove2me | solution 1 for Hirsch.joint_external_circuit_support_and_zero_deficit
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-13T23:57:47.422531+00:00
-- url     : https://prove2.me/submissions/108c2171-0be9-48bd-a1f2-191f35f8b6fc

import Mathlib

/-!
# External allocation circuits have exact support multipliers

Formalization candidate, not locally compiled. The committed toolchain is
Lean 4.30.0 / Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f.

The main theorem derives nonnegative joint packing coefficients from the full
support-minimality predicate, rather than assuming their signs. It also gives
an exact zero-deficit criterion. It does not assert catalogue completeness,
whole-set allocation sufficiency, or any ordinary-edge diameter bound.
-/
open scoped BigOperators
set_option autoImplicit false
noncomputable section

private theorem weighted_support_gap_rigidity
    {I J : Type*} [Fintype I]
    (weight : I → ℝ) (value : I → J → ℝ) (h : I → ℝ) (ν : ℝ)
    (hw : ∀ i, 0 ≤ weight i)
    (hh : ∀ i q, value i q ≤ h i)
    (hupper : ∀ q, (∑ i, weight i * value i q) ≤ ν)
    (hattained : ∃ q, ν = ∑ i, weight i * value i q) :
    0 ≤ (∑ i, weight i * h i) - ν ∧
      (((∑ i, weight i * h i) - ν = 0) ↔
        ∃ q, ∀ i, 0 < weight i → value i q = h i) := by
  classical
  obtain ⟨q₀, hq₀⟩ := hattained
  have hgap : 0 ≤ (∑ i, weight i * h i) - ν := by
    apply sub_nonneg.mpr
    rw [hq₀]
    exact Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hh i q₀) (hw i))
  refine ⟨hgap, ?_⟩
  constructor
  · intro hz
    refine ⟨q₀, ?_⟩
    intro i hi
    have hnon : ∀ j, 0 ≤ weight j * (h j - value j q₀) :=
      fun j => mul_nonneg (hw j) (sub_nonneg.mpr (hh j q₀))
    have hsum : (∑ j, weight j * (h j - value j q₀)) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      linarith
    have hle := Finset.single_le_sum (fun j _ => hnon j) (Finset.mem_univ i)
    rw [hsum] at hle
    have hprod : weight i * (h i - value i q₀) = 0 :=
      le_antisymm hle (hnon i)
    have hdiff : h i - value i q₀ = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hi)
    exact (sub_eq_zero.mp hdiff).symm
  · rintro ⟨q, hq⟩
    have he : (∑ i, weight i * h i) = ∑ i, weight i * value i q := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : weight i = 0
      · simp [hi]
      · have hpos : 0 < weight i := lt_of_le_of_ne (hw i) (Ne.symm hi)
        rw [hq i hpos]
    have hle := hupper q
    rw [← he] at hle
    exact sub_eq_zero.mpr (le_antisymm hle (sub_nonneg.mp hgap))

/-- A full internal simplex dependence cannot be contained in the support of
an external support-minimal nonnegative allocation dependence. -/
private theorem external_circuit_zero_in_each_block
    (m r k : ℕ) (a : Fin m → Fin r → Fin k → ℝ)
    (w : (Fin m ⊕ (Fin r × Option (Fin k))) → ℝ)
    (hexternal : ∃ i, w (.inl i) ≠ 0)
    (hminimal : ∀ y : (Fin m ⊕ (Fin r × Option (Fin k))) → ℝ,
      (∀ q, 0 ≤ y q) →
      (∀ l j, -(∑ i, y (.inl i) * a i l j) -
        y (.inr (l, some j)) + y (.inr (l, none)) = 0) →
      y ≠ 0 → Function.support y ⊆ Function.support w →
        Function.support w ⊆ Function.support y)
    (l : Fin r) : ∃ q : Option (Fin k), w (.inr (l, q)) = 0 := by
  classical
  by_contra hnone
  have hne : ∀ q : Option (Fin k), w (.inr (l, q)) ≠ 0 := by
    intro q hq
    exact hnone ⟨q, hq⟩
  let y : (Fin m ⊕ (Fin r × Option (Fin k))) → ℝ := fun q =>
    match q with
    | .inl _ => 0
    | .inr p => if p.1 = l then 1 else 0
  have hy : ∀ q, 0 ≤ y q := by
    intro q
    cases q with
    | inl i => simp [y]
    | inr p => dsimp [y]; split_ifs <;> norm_num
  have hkernel : ∀ l' j, -(∑ i, y (.inl i) * a i l' j) -
      y (.inr (l', some j)) + y (.inr (l', none)) = 0 := by
    intro l' j
    simp [y]
  have hyne : y ≠ 0 := by
    intro he
    have hv := congrFun he (.inr (l, none))
    simpa [y] using hv
  have hsub : Function.support y ⊆ Function.support w := by
    intro q hq
    change y q ≠ 0 at hq
    change w q ≠ 0
    cases q with
    | inl i => exact False.elim (hq (by simp [y]))
    | inr p =>
      rcases p with ⟨l', q'⟩
      by_cases he : l' = l
      · subst l'
        exact hne q'
      · exact False.elim (hq (by simp [y, he]))
  have hback := hminimal y hy hkernel hyne hsub
  obtain ⟨i, hi⟩ := hexternal
  have hiy : y (.inl i) ≠ 0 := hback hi
  exact hiy (by simp [y])

/-- The total multiplier of each block is the exact support value of the
combined original rows. Its subadditivity deficit is nonnegative, and vanishes
exactly when all positively weighted rows share a maximizing listed point. -/
theorem solution
    (m r k : ℕ) (a : Fin m → Fin r → Fin k → ℝ)
    (w : (Fin m ⊕ (Fin r × Option (Fin k))) → ℝ)
    (hw : ∀ q, 0 ≤ w q)
    (hkernel : ∀ l j, -(∑ i, w (.inl i) * a i l j) -
      w (.inr (l, some j)) + w (.inr (l, none)) = 0)
    (hexternal : ∃ i, w (.inl i) ≠ 0)
    (hminimal : ∀ y : (Fin m ⊕ (Fin r × Option (Fin k))) → ℝ,
      (∀ q, 0 ≤ y q) →
      (∀ l j, -(∑ i, y (.inl i) * a i l j) -
        y (.inr (l, some j)) + y (.inr (l, none)) = 0) →
      y ≠ 0 → Function.support y ⊆ Function.support w →
        Function.support w ⊆ Function.support y) :
    ∀ l,
      (0 ≤ w (.inr (l, none)) ∧
        (∀ j, (∑ i, w (.inl i) * a i l j) ≤ w (.inr (l, none))) ∧
        (w (.inr (l, none)) = 0 ∨
          ∃ j, w (.inr (l, none)) = ∑ i, w (.inl i) * a i l j)) ∧
      ∀ h : Fin m → ℝ, (∀ i, 0 ≤ h i) → (∀ i j, a i l j ≤ h i) →
        0 ≤ (∑ i, w (.inl i) * h i) - w (.inr (l, none)) ∧
        (((∑ i, w (.inl i) * h i) - w (.inr (l, none)) = 0) ↔
          ∃ q : Option (Fin k), ∀ i, 0 < w (.inl i) →
            (match q with | none => 0 | some j => a i l j) = h i) := by
  classical
  intro l
  have hu : ∀ j, (∑ i, w (.inl i) * a i l j) ≤ w (.inr (l, none)) := by
    intro j
    have hk := hkernel l j
    have hm := hw (.inr (l, some j))
    linarith
  obtain ⟨q, hq⟩ := external_circuit_zero_in_each_block m r k a w hexternal hminimal l
  let value : Fin m → Option (Fin k) → ℝ := fun i q =>
    match q with | none => 0 | some j => a i l j
  have hattained : w (.inr (l, none)) = ∑ i, w (.inl i) * value i q := by
    cases q with
    | none => simpa [value] using hq
    | some j =>
      have hk := hkernel l j
      simp only [hq] at hk
      dsimp [value]
      linarith
  refine ⟨⟨hw _, hu, ?_⟩, ?_⟩
  · cases q with
    | none => left; simpa [value] using hattained
    | some j => right; exact ⟨j, by simpa [value] using hattained⟩
  · intro h hh hdom
    have hv : ∀ i q', value i q' ≤ h i := by
      intro i q'
      cases q' with
      | none => exact hh i
      | some j => exact hdom i j
    have hvu : ∀ q', (∑ i, w (.inl i) * value i q') ≤ w (.inr (l, none)) := by
      intro q'
      cases q' with
      | none => simpa [value] using hw (.inr (l, none))
      | some j => exact hu j
    simpa only [value] using weighted_support_gap_rigidity
      (fun i => w (.inl i)) value h (w (.inr (l, none)))
      (fun i => hw (.inl i)) hv hvu ⟨q, hattained⟩

#print axioms weighted_support_gap_rigidity
#print axioms external_circuit_zero_in_each_block
#print axioms solution

/-- Purely internal multipliers give automatic inequalities for nonnegative
scales. They must not be mislabeled as having nonnegative deficit coefficients. -/
theorem Hirsch.joint_internal_budget_nonnegative
    (m r k : ℕ) (w : (Fin m ⊕ (Fin r × Option (Fin k))) → ℝ)
    (b : Fin m → ℝ) (h : Fin m → Fin r → ℝ) (t : Fin r → ℝ)
    (horiginal : ∀ i, w (.inl i) = 0)
    (hν : ∀ l, 0 ≤ w (.inr (l, none))) (ht : ∀ l, 0 ≤ t l) :
    0 ≤ (∑ i, w (.inl i) * b i) -
      ∑ l, ((∑ i, w (.inl i) * h i l) - w (.inr (l, none))) * t l := by
  have hp : 0 ≤ ∑ l, w (.inr (l, none)) * t l :=
    Finset.sum_nonneg (fun l _ => mul_nonneg (hν l) (ht l))
  simpa only [horiginal, zero_mul, Finset.sum_const_zero, zero_sub,
    neg_mul, Finset.sum_neg_distrib, neg_neg] using hp

#print axioms Hirsch.joint_internal_budget_nonnegative
