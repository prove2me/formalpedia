-- Prove2me | solution 1 for ECMParity.card_sqrt_fiber_mod_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T12:37:50.602241+00:00
-- url     : https://prove2.me/submissions/56dd453e-d76b-4056-859d-26b5b3b79f3d

-- Sol generated from Algebra/ECMParityCore.lean
import Mathlib
import Definitions.Def_Algebra_ECMParityCore
/-
# ECM-PARITY, core: the parity of the point count of `y² = x³ + A x + B`

For an odd prime `p` and `A B : ZMod p` put

  `curveCard A B = 1 + #{(x,y) ∈ (ZMod p)² : y² = x³ + A x + B}`

(the `1` is the point at infinity of the projective Weierstrass model).

The main result of this file is the **parity dichotomy**

  `2 ∣ curveCard A B  ↔  the cubic x³ + A x + B has a root in ZMod p`

valid whenever the cubic is separable (`Δ = -4A³ - 27B² ≠ 0`).  Equivalently:
`#E` is odd exactly when Frobenius is a `3`-cycle on the roots of the cubic
(the cubic is irreducible over `𝔽_p`; see `ECMParityFrobenius.lean`).

The proof is elementary and self-contained:

* fibrewise counting: over each `x` the fibre `{y : y² = f x}` has odd
  cardinality iff `f x = 0`, hence `#affine ≡ #roots (mod 2)`;
* a separable cubic has `0`, `1` or `3` roots (never `2`), so `#roots` is odd
  iff `#roots ≠ 0`.

§0 collects the purely algebraic facts about a depressed cubic over an arbitrary
field (Vieta, the third root, the discriminant as a square of the root
difference product).  These are reused over the cubic extension `𝔽_{p³}` in
`ECMParityFrobenius.lean`.
-/

open ECMParity

open Finset

/-! ## 0. Depressed cubics over an arbitrary field -/




variable {F : Type*} [Field F] {A B a b x : F}









/-! ## 1. Fibrewise counting over `𝔽_p` -/

variable {p : ℕ} [Fact p.Prime]




theorem two_ne_zero_of_odd (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have hp' : p.Prime := Fact.out
  exact hp ((Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).1 h2)




/-! ## 2. A separable cubic has `0`, `1` or `3` roots -/




/-! ## 3. The parity dichotomy -/




open ECMParity in
theorem solution(hp : p ≠ 2) (c : ZMod p) :
    (((univ.filter (fun y : ZMod p => y ^ 2 = c)).card : ZMod 2)) =
      if c = 0 then 1 else 0 := by
  have hp2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_odd hp
  by_cases hc : c = 0
  · subst hc
    have hset : (univ.filter (fun y : ZMod p => y ^ 2 = 0)) = {0} := by
      ext y; simp [pow_eq_zero_iff]
    rw [hset]
    simp
  · simp only [hc, if_false]
    by_cases hs : ∃ y₀ : ZMod p, y₀ ^ 2 = c
    · obtain ⟨y₀, hy₀⟩ := hs
      have hy0 : y₀ ≠ 0 := by
        rintro rfl; exact hc (by simpa using hy₀.symm)
      have hne : y₀ ≠ -y₀ := by
        intro h
        apply hy0
        have h2 : (2 : ZMod p) * y₀ = 0 := by linear_combination h
        rcases mul_eq_zero.1 h2 with h' | h'
        · exact absurd h' hp2
        · exact h'
      have hset : (univ.filter (fun y : ZMod p => y ^ 2 = c)) = {y₀, -y₀} := by
        ext y
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
        constructor
        · intro hy
          have hfac : (y - y₀) * (y + y₀) = 0 := by linear_combination hy - hy₀
          rcases mul_eq_zero.1 hfac with h | h
          · exact Or.inl (sub_eq_zero.1 h)
          · exact Or.inr (eq_neg_of_add_eq_zero_left h)
        · rintro (rfl | rfl)
          · exact hy₀
          · rw [neg_pow]; simpa using hy₀
      rw [hset, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
      decide
    · push_neg at hs
      have hset : (univ.filter (fun y : ZMod p => y ^ 2 = c)) = ∅ := by
        ext y; simp [hs y]
      simp [hset]
