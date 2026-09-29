-- Prove2me | solution 1 for Moebius.ZM.isUnit_iff_nrm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:18:32.467666+00:00
-- url     : https://prove2.me/submissions/8950597d-98fb-46eb-b655-2766f8971a00

-- Sol generated from MachineLearning/MoebiusTwistRing.lean
import Mathlib
import Definitions.Def_MachineLearning_MoebiusTwistRing

/-!
# The Möbius Twist Ring `ZM = ℤ[t]/(t² − 1)`

This file develops the *correct* algebraic home of the "Möbius integers" idea:
the ring obtained from `ℤ` by adjoining a formal orientation-reversing symbol
`t` with `t² = 1` (the holonomy of the Möbius band's orientation double cover).

We realise `ℤ[t]/(t²−1)` concretely as the subring

  `evenDiff = {(u, v) ∈ ℤ × ℤ | u ≡ v (mod 2)}`

via `a + b·t ↦ (a + b, a − b)` (the "characters of ℤ/2" coordinates).  This gives
the `CommRing` structure for free and makes every computation transparent.

## Main results

* `ZM.mk_mul`, `ZM.mk_add` — the twisted multiplication `(a,b)(c,d) = (ac+bd, ad+bc)`.
* `ZM.tw_sq`, `ZM.isUnit_tw`, `ZM.not_prime_tw` — the twist `t` is a unit of order 2,
  hence **not** a prime: "orientation is a unit, not a prime".
* `ZM.not_domain` — `ZM` is not an integral domain: `(1+t)(1−t) = 0`.
* `ZM.nrm_mul`, `ZM.isUnit_iff_nrm`, `ZM.isUnit_mk_iff` — the norm `N(a+bt) = a² − b²`
  is multiplicative and detects units; the unit group is `{±1, ±t} ≅ (ℤ/2)²`.
* `ZM.nrm_ne_two` — no element has norm `±2`; consequently `ZM.irreducible_two`.
* `ZM.irreducible_mk_int_iff` — a rational integer is irreducible in `ZM` **iff** it is
  `±2`: the twist ring destroys the primality of every odd prime.
* `ZM.odd_prime_splits` — every odd integer `2k+1` factors nontrivially in `ZM`,
  e.g. `3 = (2 + t)(2 − t)`; so `6 = 2·(2+t)·(2−t)` has **three** irreducible factors.
* `ZM.idempotent_eq` and `ZM.not_ringEquiv_prod` — `ZM` has no nontrivial idempotents,
  hence `ZM ≇ ℤ × ℤ`: the Möbius extension of `ℤ` by its twist does not split.
* `ZM.tw_pow_eq_one_iff` — holonomy: `t^n = 1 ↔ n` even, matching `σ² = id` for the
  deck transformation `σ(x,y) = (x+1,−y)` of the Möbius band.
-/

open Moebius



open ZM



lemma ext_coe {x y : ZM} (h : (x : ℤ × ℤ) = y) : x = y := Subtype.ext h














/-! ### Failure of the domain property -/



/-! ### The norm -/



@[simp] lemma nrm_mul (x y : ZM) : nrm (x * y) = nrm x * nrm y := by
  simp only [nrm, Subring.coe_mul, Prod.fst_mul, Prod.snd_mul]
  ring

@[simp] lemma nrm_one : nrm (1 : ZM) = 1 := by simp [nrm]






/-! ### Factorisation experiments: 6, −6, and the twist -/















/-! ### No nontrivial idempotents: the Möbius extension does not split -/



/-! ### Holonomy of the Möbius band -/





open Moebius in
theorem solution(z : ZM) : IsUnit z ↔ nrm z = 1 ∨ nrm z = -1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have hmul : (u : ZM) * (↑u⁻¹ : ZM) = 1 := u.mul_inv
    have h : nrm (u : ZM) * nrm (↑u⁻¹ : ZM) = 1 := by
      rw [← nrm_mul, hmul, nrm_one]
    exact Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ h)
  · intro h
    refine IsUnit.of_mul_eq_one z ?_
    have hu : (z : ℤ × ℤ).1 * (z : ℤ × ℤ).2 = 1 ∨ (z : ℤ × ℤ).1 * (z : ℤ × ℤ).2 = -1 := h
    have h1 : (z : ℤ × ℤ).1 = 1 ∧ (z : ℤ × ℤ).2 = 1 ∨
        (z : ℤ × ℤ).1 = -1 ∧ (z : ℤ × ℤ).2 = -1 ∨
        (z : ℤ × ℤ).1 = 1 ∧ (z : ℤ × ℤ).2 = -1 ∨
        (z : ℤ × ℤ).1 = -1 ∧ (z : ℤ × ℤ).2 = 1 := by
      rcases hu with hu | hu
      · rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · rcases Int.mul_eq_neg_one_iff_eq_one_or_neg_one.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))
    apply ext_coe
    have : ((z * z : ZM) : ℤ × ℤ) = ((z : ℤ × ℤ).1 * (z : ℤ × ℤ).1,
        (z : ℤ × ℤ).2 * (z : ℤ × ℤ).2) := rfl
    rw [this]
    have hone : ((1 : ZM) : ℤ × ℤ) = (1, 1) := rfl
    rw [hone]
    rcases h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      rw [ha, hb] <;> norm_num
