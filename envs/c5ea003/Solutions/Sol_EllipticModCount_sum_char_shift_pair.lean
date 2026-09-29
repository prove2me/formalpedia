-- Prove2me | solution 1 for EllipticModCount.sum_char_shift_pair
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:49:46.240763+00:00
-- url     : https://prove2.me/submissions/59e484a3-b92f-4532-a1f1-c8f211830438

-- Sol generated from Combinatorics/EllipticSecondMoment.lean
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticSecondMoment
import Theorems.Thm_EllipticModCount_sum_char_mul_shift
/-
# The exact second moment of the trace of Frobenius over a finite field

Let `F` be a finite field of odd characteristic, `q = #F`, and for `a b : F` let
`a(a,b)` be the trace of Frobenius of the short Weierstrass curve `y^2 = x^3+a*x+b`
(defined in `Combinatorics.EllipticPointCount`).  We prove the **exact** identity

`∑_{a,b ∈ F} a(a,b)^2 = q^3 - q^2`,

together with its Chebyshev consequence: the number of parameter pairs `(a,b)` with
`a(a,b)^2 ≥ K` is at most `(q^3 - q^2)/K`.  In particular *almost all* curves in the
family satisfy the Hasse bound `|a| ≤ 2√q`, by a purely elementary character-sum
computation (no Weil conjectures, no Riemann–Roch).

The engine is the elementary evaluation of the quadratic character sum of a
separable quadratic, `EllipticModCount.sum_char_mul_shift`.

Main results:

* `EllipticModCount.sum_char_mul_shift` : `∑_c χ(c(c+w)) = -1` for `w ≠ 0`.
* `EllipticModCount.sum_char_shift_pair` : `∑_b χ((b+u)(b+v)) = q-1` or `-1`.
* `EllipticModCount.second_moment_charSum` : `∑_{a,b} S(a,b)^2 = q^3 - q^2`.
* `EllipticModCount.second_moment_frobTrace` : the same for the trace of Frobenius.
* `EllipticModCount.card_large_frobTrace_le` : Chebyshev / "Hasse on average".
-/

open EllipticModCount

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]


/-- `χ(c * c)` is the indicator of `c ≠ 0`. -/
private lemma char_mul_self (c : F) :
    quadraticChar F (c * c) = if c = 0 then 0 else 1 := by
  by_cases h : c = 0
  · simp [h]
  · rw [if_neg h, ← sq]
    exact quadraticChar_sq_one' h

/-- `∑_c χ(c^2) = q - 1`. -/
theorem sum_char_sq : ∑ c : F, quadraticChar F (c * c) = (Fintype.card F : ℤ) - 1 := by
  rw [Finset.sum_congr rfl fun c _ => char_mul_self c]
  have hsplit : ∀ c : F, (if c = 0 then (0 : ℤ) else 1) = 1 - (if c = 0 then 1 else 0) := by
    intro c
    by_cases h : c = 0 <;> simp [h]
  rw [Finset.sum_congr rfl fun c _ => hsplit c, Finset.sum_sub_distrib]
  simp [Finset.card_univ]





















open EllipticModCount in
theorem solution(hF : ringChar F ≠ 2) (u v : F) :
    ∑ b : F, quadraticChar F ((b + u) * (b + v))
      = if u = v then (Fintype.card F : ℤ) - 1 else -1 := by
  have hbij : Function.Bijective fun c : F => c - u := by
    constructor
    · intro c₁ c₂ h
      simpa using h
    · intro c
      exact ⟨c + u, by ring⟩
  have hshift : ∑ c : F, quadraticChar F (c * (c + (v - u)))
      = ∑ b : F, quadraticChar F ((b + u) * (b + v)) := by
    have := Fintype.sum_bijective (fun c : F => c - u) hbij
      (fun c => quadraticChar F ((c - u + u) * (c - u + v)))
      (fun b => quadraticChar F ((b + u) * (b + v))) (fun _ => rfl)
    rw [← this]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    ring
  rw [← hshift]
  by_cases h : u = v
  · subst h
    rw [if_pos rfl]
    have hcc : ∀ c : F, c * (c + (u - u)) = c * c := by
      intro c
      ring
    rw [Finset.sum_congr rfl fun c _ => congrArg (quadraticChar F) (hcc c), sum_char_sq]
  · rw [if_neg h]
    exact sum_char_mul_shift hF (sub_ne_zero.mpr (Ne.symm h))
