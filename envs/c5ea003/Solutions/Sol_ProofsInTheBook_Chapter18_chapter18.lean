-- Prove2me | solution 1 for ProofsInTheBook.Chapter18.chapter18
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T15:18:18.60622+00:00
-- url     : https://prove2.me/submissions/a9cb0d88-72a2-4c05-afbd-beaf3a5101ab

import Mathlib


/-!
# Chapter 18: In praise of inequalities

From "Proofs from THE BOOK":

**AM-GM inequality**: the geometric mean of finitely many non-negative reals is at most
their arithmetic mean.  The two-variable case `√(ab) ≤ (a+b)/2` is the book's warm-up
(from `(√a - √b)² ≥ 0`); the headline `chapter18` is the general `n`-variable statement.

**Cauchy-Schwarz**: `(∑ aᵢbᵢ)² ≤ (∑ aᵢ²)(∑ bᵢ²)`, the discriminant inequality.
-/

namespace ProofsInTheBook.Chapter18

/-!
### AM-GM: the (a-b)² ≥ 0 trick (two-variable warm-up)
-/







/-!
### General AM-GM and Cauchy-Schwarz
-/





end ProofsInTheBook.Chapter18

open ProofsInTheBook.Chapter18

theorem solution {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (z : ι → ℝ)
    (hz : ∀ i ∈ s, 0 ≤ z i) :
    (∏ i ∈ s, z i) ^ ((s.card : ℝ)⁻¹) ≤ (∑ i ∈ s, z i) / s.card := by
  have hcard : (0 : ℝ) < s.card := by
    exact_mod_cast Finset.card_pos.mpr hs
  set w : ι → ℝ := fun _ => (s.card : ℝ)⁻¹ with hw_def
  have hw : ∀ i ∈ s, 0 ≤ w i := by
    intro i _; positivity
  have hw' : ∑ i ∈ s, w i = 1 := by
    simp only [hw_def, Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hgm := Real.geom_mean_le_arith_mean_weighted s w z hw hw' hz
  -- LHS: ∏ z i ^ (1/n) = (∏ z i) ^ (1/n)
  have hprod : ∏ i ∈ s, z i ^ ((s.card : ℝ)⁻¹) = (∏ i ∈ s, z i) ^ ((s.card : ℝ)⁻¹) :=
    Real.finsetProd_rpow s z hz _
  -- RHS: ∑ (1/n) * z i = (∑ z i) / n
  have hrhs : ∑ i ∈ s, w i * z i = (∑ i ∈ s, z i) / s.card := by
    simp only [hw_def]
    rw [← Finset.mul_sum]
    field_simp
  calc (∏ i ∈ s, z i) ^ ((s.card : ℝ)⁻¹)
      = ∏ i ∈ s, z i ^ ((s.card : ℝ)⁻¹) := hprod.symm
    _ ≤ ∑ i ∈ s, w i * z i := hgm
    _ = (∑ i ∈ s, z i) / s.card := hrhs
