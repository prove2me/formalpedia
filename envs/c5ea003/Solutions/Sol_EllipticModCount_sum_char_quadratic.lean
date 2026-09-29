-- Prove2me | solution 1 for EllipticModCount.sum_char_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:57:29.814448+00:00
-- url     : https://prove2.me/submissions/91426285-654b-4034-902d-fc5968cc835f

-- Sol generated from Combinatorics/EllipticVerticalMoment.lean
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticSecondMoment
import Definitions.Def_Combinatorics_EllipticVerticalMoment
import Theorems.Thm_EllipticModCount_sum_char_sq_sub
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
theorem solution(hF : ringChar F ≠ 2) {α : F} (hα : α ≠ 0) (β γ : F) :
    ∑ v : F, quadraticChar F (α * v ^ 2 + β * v + γ)
      = if β ^ 2 - 4 * α * γ = 0 then ((Fintype.card F : ℤ) - 1) * quadraticChar F α
        else -quadraticChar F α := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h4 : (4 : F) ≠ 0 := by
    have he : (4 : F) = 2 * 2 := by norm_num
    rw [he]
    exact mul_ne_zero h2 h2
  set D : F := β ^ 2 / 4 - α * γ with hD
  have hchi : ∀ v : F, quadraticChar F (α * v ^ 2 + β * v + γ)
      = quadraticChar F α * quadraticChar F ((α * v + β / 2) ^ 2 - D) := by
    intro v
    have hid : (α * v + β / 2) ^ 2 - D = α * (α * v ^ 2 + β * v + γ) := by
      rw [hD]
      field_simp
      ring
    rw [hid, map_mul, ← mul_assoc, ← sq, quadraticChar_sq_one hα, one_mul]
  have hbij : Function.Bijective fun v : F => α * v + β / 2 := by
    constructor
    · intro v₁ v₂ h
      simp only at h
      have hv : α * v₁ = α * v₂ := by linear_combination h
      exact mul_left_cancel₀ hα hv
    · intro u
      refine ⟨(u - β / 2) / α, ?_⟩
      field_simp
      ring
  have hre : ∑ v : F, quadraticChar F ((α * v + β / 2) ^ 2 - D)
      = ∑ u : F, quadraticChar F (u ^ 2 - D) :=
    Fintype.sum_bijective _ hbij _ _ fun _ => rfl
  rw [Finset.sum_congr rfl fun v _ => hchi v, ← Finset.mul_sum, hre, sum_char_sq_sub hF]
  have hDiff : (D = 0) ↔ (β ^ 2 - 4 * α * γ = 0) := by
    rw [hD]
    constructor
    · intro h
      field_simp at h
      linear_combination h
    · intro h
      field_simp
      linear_combination h
  by_cases hc : β ^ 2 - 4 * α * γ = 0
  · rw [if_pos hc, if_pos (hDiff.mpr hc)]
    ring
  · rw [if_neg hc, if_neg (fun hx => hc (hDiff.mp hx))]
    ring
