-- Prove2me | Theorems.Thm_ParityGap_pi_dvd_natCast_p
-- name    : ParityGap.pi_dvd_natCast_p
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:46:20.01216+00:00
-- url     : https://prove2.me/theorems/d83e791d-aabd-47c4-9612-1140a0b5a573
-- title:
--   `π = ζ - 1` divides `p` in `ℤ[ζ_p]`.
-- statement:
--   `π = ζ - 1` divides `p` in `ℤ[ζ_p]`.
--
--   ```lean
--   theorem ParityGap.pi_dvd_natCast_p: pi p ∣ (p : CycRing p) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/CyclotomicRing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/CyclotomicRing.lean#L104

-- Thm stub generated from Probability/CyclotomicRing.lean
import Mathlib
import Definitions.Def_Probability_CyclotomicRing
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

open ParityGap

variable (p : ℕ) [hp : Fact p.Prime]

theorem ParityGap.pi_dvd_natCast_p: pi p ∣ (p : CycRing p) := by sorry
