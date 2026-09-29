-- Prove2me | Definitions.Def_Probability_CyclotomicRing
-- name    : Probability_CyclotomicRing
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:11:43.549357+00:00
-- url     : https://prove2.me/theorems/81cdbde9-2b0f-4c41-87a7-876fd4c78df9
-- title:
--   Aether Catalog definitions — Probability_CyclotomicRing
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.CyclotomicRing`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/CyclotomicRing.lean by skeleton subtraction
import Mathlib
/-
# The ring `ℤ[ζ_p]` and its reduction modulo the prime `ζ - 1`

For the parity-gap / Chebotarev development we need an honest characteristic-zero model of
`ℤ[ζ_p]`, together with the reduction map onto `𝔽_p` that sends `ζ ↦ 1`.  Everything is built
by hand from `AdjoinRoot (cyclotomic p ℤ)`, so no algebraic number theory is imported:

* `ParityGap.CycRing p` — the ring `ℤ[X]/(Φ_p)`, a Noetherian domain;
* `ParityGap.zeta p` — the image of `X`, a primitive `p`-th root of unity in `CycRing p`;
* `ParityGap.red p : CycRing p →+* ZMod p` — the reduction sending `ζ ↦ 1`;
* `ParityGap.pi p = ζ - 1` — the ramified prime, with `red` vanishing exactly on multiples of it
  (`ParityGap.pi_dvd_of_red_eq_zero`);
* `ParityGap.exists_primitive_scaling` — every nonzero vector over `CycRing p` can be divided by
  a power of `π` so that at least one coordinate survives reduction.  This uses the Krull
  intersection theorem, which is where Noetherianity enters.
-/


open Polynomial

namespace ParityGap

variable (p : ℕ) [hp : Fact p.Prime]

/-- `ℤ[ζ_p] = ℤ[X] / (Φ_p)`. -/
abbrev CycRing : Type := AdjoinRoot (cyclotomic p ℤ)

instance instIsDomainCycRing : IsDomain (CycRing p) := by
  have hprime : Prime (cyclotomic p ℤ) := (cyclotomic.irreducible hp.out.pos).prime
  have : (Ideal.span {cyclotomic p ℤ}).IsPrime :=
    (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  exact Ideal.Quotient.isDomain _

/-- The distinguished primitive `p`-th root of unity. -/
noncomputable def zeta : CycRing p := AdjoinRoot.root (cyclotomic p ℤ)

/-- The uniformiser at the unique prime above `p`. -/
noncomputable def pi : CycRing p := zeta p - 1







/-- The reduction `ℤ[ζ_p] → 𝔽_p` determined by `ζ ↦ 1`. -/
noncomputable def red : CycRing p →+* ZMod p :=
  AdjoinRoot.lift (Int.castRingHom (ZMod p)) 1 (by
    rw [eval₂_at_one, eval_one_cyclotomic_prime]
    simp)










end ParityGap


