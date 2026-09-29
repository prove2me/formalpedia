-- Prove2me | Theorems.Thm_ParityGap_exists_primitive_scaling
-- name    : ParityGap.exists_primitive_scaling
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:47:41.802618+00:00
-- url     : https://prove2.me/theorems/a44c5cf2-a49c-41cd-81fe-de779d67f910
-- title:
--   Primitive scaling.
-- statement:
--   **Primitive scaling.**  A nonzero vector over `ℤ[ζ_p]` can be divided by a power of `π` so
--   that some coordinate has nonzero reduction.
--
--   ```lean
--   theorem ParityGap.exists_primitive_scaling{ι : Type*} [Fintype ι] (v : ι → CycRing p)
--       (hv : ∃ i, v i ≠ 0) :
--       ∃ (m : ℕ) (w : ι → CycRing p), (∀ i, v i = pi p ^ m * w i) ∧ ∃ i, red p (w i) ≠ 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/CyclotomicRing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/CyclotomicRing.lean#L176

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

theorem ParityGap.exists_primitive_scaling{ι : Type*} [Fintype ι] (v : ι → CycRing p)
    (hv : ∃ i, v i ≠ 0) :
    ∃ (m : ℕ) (w : ι → CycRing p), (∀ i, v i = pi p ^ m * w i) ∧ ∃ i, red p (w i) ≠ 0 := by sorry
