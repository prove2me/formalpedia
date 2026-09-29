-- Prove2me | solution 1 for Moebius.ZM.irreducible_of_prime_natAbs
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:22:34.989993+00:00
-- url     : https://prove2.me/submissions/3b46fb49-1b0d-44fe-ad8a-9de9ab73188b

-- Sol generated from MachineLearning/MoebiusTwistRing.lean
import Mathlib
import Definitions.Def_MachineLearning_MoebiusTwistRing
import Theorems.Thm_Moebius_ZM_isUnit_iff_nrm

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







/-! ### Factorisation experiments: 6, −6, and the twist -/















/-! ### No nontrivial idempotents: the Möbius extension does not split -/



/-! ### Holonomy of the Möbius band -/





open Moebius in
theorem solution{z : ZM} (h : Nat.Prime (nrm z).natAbs) :
    Irreducible z := by
  constructor
  · rw [isUnit_iff_nrm]
    rintro (hz | hz) <;> rw [hz] at h <;>
      exact Nat.not_prime_one (by simpa using h)
  · intro x y hxy
    have hn : nrm x * nrm y = nrm z := by rw [hxy, nrm_mul]
    have hnat : (nrm x).natAbs * (nrm y).natAbs = (nrm z).natAbs := by
      rw [← Int.natAbs_mul, hn]
    rcases Nat.Prime.eq_one_or_self_of_dvd h (nrm x).natAbs ⟨_, hnat.symm⟩ with h1 | h1
    · left
      rw [isUnit_iff_nrm]
      omega
    · right
      have hpos : 0 < (nrm z).natAbs := h.pos
      have hy : (nrm y).natAbs = 1 := by
        rw [h1] at hnat
        have h2 : (nrm z).natAbs * (nrm y).natAbs = (nrm z).natAbs * 1 := by
          simpa using hnat
        exact Nat.eq_of_mul_eq_mul_left hpos h2
      rw [isUnit_iff_nrm]
      omega
