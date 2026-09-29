-- Prove2me | Definitions.Def_MachineLearning_MoebiusTwistRing
-- name    : MachineLearning_MoebiusTwistRing
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:47:36.435416+00:00
-- url     : https://prove2.me/theorems/a3f05ad1-5fd2-4ca2-9231-713b51d297a7
-- title:
--   Aether Catalog definitions — MachineLearning_MoebiusTwistRing
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.MoebiusTwistRing`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/MoebiusTwistRing.lean by skeleton subtraction
import Mathlib

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

namespace Moebius

/-- The subring `{(u,v) : u ≡ v mod 2}` of `ℤ × ℤ`; it is the image of
`ℤ[t]/(t²−1)` under the two characters of `ℤ/2`. -/
def evenDiff : Subring (ℤ × ℤ) where
  carrier := {p | Even (p.1 - p.2)}
  mul_mem' := by
    intro p q hp hq
    simp only [Set.mem_setOf_eq, Int.even_sub, Prod.fst_mul, Prod.snd_mul,
      Int.even_mul] at *
    tauto
  one_mem' := by simp [Set.mem_setOf_eq]
  add_mem' := by
    intro p q hp hq
    simp only [Set.mem_setOf_eq] at *
    have h : p.1 + q.1 - (p.2 + q.2) = (p.1 - p.2) + (q.1 - q.2) := by ring
    simpa [Prod.fst_add, Prod.snd_add, h] using hp.add hq
  zero_mem' := by simp [Set.mem_setOf_eq]
  neg_mem' := by
    intro p hp
    simp only [Set.mem_setOf_eq] at *
    have h : -p.1 - -p.2 = -(p.1 - p.2) := by ring
    simpa [Prod.fst_neg, Prod.snd_neg, h] using hp.neg

/-- The Möbius twist ring `ZM = ℤ[t]/(t² − 1)`. -/
abbrev ZM : Type := evenDiff

namespace ZM

/-- `mk a b` is the element `a + b·t`, in character coordinates `(a+b, a−b)`. -/
def mk (a b : ℤ) : ZM := ⟨(a + b, a - b), by
  have h : a + b - (a - b) = 2 * b := by ring
  simp only [evenDiff, Set.mem_setOf_eq, Subring.mem_mk, Subsemiring.mem_mk,
    Submonoid.mem_mk, Subsemigroup.mem_mk]
  rw [h]
  exact ⟨b, by ring⟩⟩










/-- The twist element `t`, i.e. the class of the orientation-reversing generator. -/
def tw : ZM := mk 0 1






/-! ### Failure of the domain property -/



/-! ### The norm -/

/-- The norm `N(a + b t) = a² − b²`, i.e. the product of the two characters. -/
def nrm (z : ZM) : ℤ := (z : ℤ × ℤ).1 * (z : ℤ × ℤ).2









/-! ### Factorisation experiments: 6, −6, and the twist -/















/-! ### No nontrivial idempotents: the Möbius extension does not split -/



/-! ### Holonomy of the Möbius band -/



end ZM

end Moebius


