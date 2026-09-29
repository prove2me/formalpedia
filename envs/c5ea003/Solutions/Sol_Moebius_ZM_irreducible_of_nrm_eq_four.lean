-- Prove2me | solution 1 for Moebius.ZM.irreducible_of_nrm_eq_four
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:20:41.742986+00:00
-- url     : https://prove2.me/submissions/a5726165-6810-4c2b-adb5-a3b33e745b3d

-- Sol generated from MachineLearning/MoebiusTwistRing.lean
import Mathlib
import Definitions.Def_MachineLearning_MoebiusTwistRing
import Theorems.Thm_Moebius_ZM_isUnit_iff_nrm
import Theorems.Thm_Moebius_ZM_nrm_ne_two

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

















/-! ### Failure of the domain property -/



/-! ### The norm -/



@[simp] lemma nrm_mul (x y : ZM) : nrm (x * y) = nrm x * nrm y := by
  simp only [nrm, Subring.coe_mul, Prod.fst_mul, Prod.snd_mul]
  ring





/-- An auxiliary arithmetic fact: a factorisation of `4` in `ℕ` avoiding the
factor `2` must contain the factor `1`. -/
private lemma nat_factor_four {a b : ℕ} (h : a * b = 4) (ha : a ≠ 2) : a = 1 ∨ b = 1 := by
  have hle : a ≤ 4 := Nat.le_of_dvd (by omega) ⟨b, h.symm⟩
  interval_cases a <;> omega


/-! ### Factorisation experiments: 6, −6, and the twist -/















/-! ### No nontrivial idempotents: the Möbius extension does not split -/



/-! ### Holonomy of the Möbius band -/





open Moebius in
theorem solution{z : ZM} (hz : nrm z = 4) : Irreducible z := by
  constructor
  · rw [isUnit_iff_nrm, hz]
    norm_num
  · intro x y hxy
    have hn : nrm x * nrm y = 4 := by
      rw [← hz, hxy, nrm_mul]
    have hx2 := nrm_ne_two x
    have hy2 := nrm_ne_two y
    have habs : (nrm x).natAbs * (nrm y).natAbs = 4 := by
      rw [← Int.natAbs_mul, hn]
      rfl
    have hxne : (nrm x).natAbs ≠ 2 := by omega
    have hyne : (nrm y).natAbs ≠ 2 := by omega
    have hx : nrm x = 1 ∨ nrm x = -1 ∨ nrm y = 1 ∨ nrm y = -1 := by
      rcases nat_factor_four habs hxne with h1 | h1 <;> omega
    rcases hx with h | h | h | h
    · exact Or.inl ((isUnit_iff_nrm x).mpr (Or.inl h))
    · exact Or.inl ((isUnit_iff_nrm x).mpr (Or.inr h))
    · exact Or.inr ((isUnit_iff_nrm y).mpr (Or.inl h))
    · exact Or.inr ((isUnit_iff_nrm y).mpr (Or.inr h))
