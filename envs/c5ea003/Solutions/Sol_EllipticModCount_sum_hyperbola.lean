-- Prove2me | solution 1 for EllipticModCount.sum_hyperbola
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:54:08.680744+00:00
-- url     : https://prove2.me/submissions/cc6ed1b9-6313-4046-a823-2d1feb4d4096

-- Sol generated from Combinatorics/EllipticVerticalMoment.lean
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticSecondMoment
import Definitions.Def_Combinatorics_EllipticVerticalMoment
/-
# Quadratic character sums, conic counts, and the exact vertical second moment

This file completes the elementary toolkit for the family `y^2 = x^3 + a*x + b` over a
finite field `F` of characteristic `≠ 2, 3` by evaluating **every** quadratic character
sum of a quadratic polynomial, counting the points of the conic `x^2+x*y+y^2 = c`, and
deducing the **exact vertical second moment**

`∑_{b ∈ F} a(a,b)^2 = q^2 - q * (1 + χ(-3) + χ(-3a))`  for `a ≠ 0`,
`∑_{b ∈ F} a(0,b)^2 = q * (q-1) * (1 + χ(-3))`.

The second formula gives a second, independent proof that the family `y^2 = x^3 + b` is
supersingular exactly when `χ(-3) = -1`, i.e. when `q ≡ 2 (mod 3)`.

Main results:

* `EllipticModCount.sum_char_quadratic` : `∑_v χ(αv^2+βv+γ) = -χ(α)` unless the
  discriminant vanishes, in which case it is `(q-1)χ(α)`.
* `EllipticModCount.sum_conic` : the number of points of `x^2+xy+y^2 = c`.
* `EllipticModCount.collisions_eq` / `collisions_zero` : exact collision counts.
* `EllipticModCount.vertical_second_moment` / `vertical_second_moment_zero`.
* `EllipticModCount.vertical_second_moment_zero_eq_zero_iff` : supersingularity of the
  family `y^2 = x^3 + b` is *equivalent* to `χ(-3) = -1`.
-/

open EllipticModCount

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]



























open EllipticModCount in
theorem solution(hF : ringChar F ≠ 2) (D : F) :
    ∑ u : F, ∑ t : F, (if t ^ 2 = u ^ 2 - D then (1 : ℤ) else 0)
      = if D = 0 then 2 * (Fintype.card F : ℤ) - 1 else (Fintype.card F : ℤ) - 1 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hconv : (∑ u : F, ∑ t : F, (if t ^ 2 = u ^ 2 - D then (1 : ℤ) else 0))
      = ∑ ut : F × F, (if ut.2 ^ 2 = ut.1 ^ 2 - D then (1 : ℤ) else 0) :=
    (Fintype.sum_prod_type' (fun u t : F => if t ^ 2 = u ^ 2 - D then (1 : ℤ) else 0)).symm
  have hbij : Function.Bijective
      (fun sr : F × F => (((sr.1 + sr.2) / 2, (sr.2 - sr.1) / 2) : F × F)) := by
    refine Function.bijective_iff_has_inverse.mpr
      ⟨fun ut : F × F => ((ut.1 - ut.2, ut.1 + ut.2) : F × F), ?_, ?_⟩
    · rintro ⟨s, r⟩
      simp only [Prod.mk.injEq]
      constructor <;> field_simp <;> ring
    · rintro ⟨u, t⟩
      simp only [Prod.mk.injEq]
      constructor <;> field_simp <;> ring
  have hstep : ∀ sr : F × F,
      (if ((sr.2 - sr.1) / 2) ^ 2 = ((sr.1 + sr.2) / 2) ^ 2 - D then (1 : ℤ) else 0)
        = (if sr.1 * sr.2 = D then (1 : ℤ) else 0) := by
    rintro ⟨s, r⟩
    refine if_congr ?_ rfl rfl
    have hid : ((s + r) / 2) ^ 2 - ((r - s) / 2) ^ 2 = s * r := by
      field_simp
      ring
    constructor
    · intro h
      linear_combination -hid - h
    · intro h
      linear_combination -hid - h
  have hre : ∑ sr : F × F, (if sr.1 * sr.2 = D then (1 : ℤ) else 0)
      = ∑ ut : F × F, (if ut.2 ^ 2 = ut.1 ^ 2 - D then (1 : ℤ) else 0) := by
    rw [← Fintype.sum_bijective _ hbij
      (fun sr : F × F => if ((sr.2 - sr.1) / 2) ^ 2 = ((sr.1 + sr.2) / 2) ^ 2 - D then (1 : ℤ)
        else 0)
      (fun ut : F × F => if ut.2 ^ 2 = ut.1 ^ 2 - D then (1 : ℤ) else 0) (fun _ => rfl)]
    exact Finset.sum_congr rfl fun sr _ => (hstep sr).symm
  rw [hconv, ← hre, Fintype.sum_prod_type]
  have hinner : ∀ s : F, ∑ r : F, (if s * r = D then (1 : ℤ) else 0)
      = if s = 0 then (if D = 0 then (Fintype.card F : ℤ) else 0) else 1 := by
    intro s
    by_cases hs : s = 0
    · subst hs
      rw [if_pos rfl]
      by_cases hD : D = 0
      · subst hD
        simp [Finset.card_univ]
      · simp [hD, Ne.symm hD]
    · rw [if_neg hs]
      have hiff : ∀ r : F, (s * r = D) ↔ (r = s⁻¹ * D) := by
        intro r
        constructor
        · intro h
          field_simp
          linear_combination h
        · intro h
          rw [h]
          field_simp
      rw [Finset.sum_congr rfl fun r _ => if_congr (hiff r) rfl rfl]
      simp
  have hfin : ∀ X : ℤ, (∑ _s : F, (0 : ℤ)) = 0 → (∑ s : F, (if s = 0 then X else (1 : ℤ)))
      = X + ((Fintype.card F : ℤ) - 1) := by
    intro X _
    have hsplit : ∀ s : F, (if s = 0 then X else (1 : ℤ))
        = 1 + (if s = 0 then X - 1 else 0) := by
      intro s
      by_cases h : s = 0 <;> simp [h]
    rw [Finset.sum_congr rfl fun s _ => hsplit s, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one,
      Finset.sum_ite_eq' univ (0 : F) (fun _ : F => X - 1)]
    simp
    ring
  rw [Finset.sum_congr rfl fun s _ => hinner s, hfin _ (by simp)]
  by_cases hD : D = 0
  · rw [if_pos hD, if_pos hD]
    ring
  · rw [if_neg hD, if_neg hD]
    ring
