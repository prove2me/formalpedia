-- Prove2me | Theorems.Thm_ResidueDial_crtDial_density
-- name    : ResidueDial.crtDial_density
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:58:18.810648+00:00
-- url     : https://prove2.me/theorems/801a17c5-fa20-4378-8b80-da9fe093ed80
-- title:
--   Densities multiply under CRT composition.
-- statement:
--   **Densities multiply under CRT composition.**  The battery's density is the
--   product of the dial densities — this is the only way the composition enters the
--   law.
--
--   ```lean
--   theorem ResidueDial.crtDial_density{m n : ℕ} [NeZero m] [NeZero n] (h : Nat.Coprime m n)
--       (K₁ : Finset (ZMod m)ˣ) (K₂ : Finset (ZMod n)ˣ) :
--       density (m * n) (crtDial h K₁ K₂) = density m K₁ * density n K₂ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/ResidueDial/Battery.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/ResidueDial/Battery.lean#L68

-- Thm stub generated from Cryptography/ResidueDial/Battery.lean
import Mathlib
import Definitions.Def_Cryptography_ResidueDial_Battery
import Definitions.Def_Cryptography_ResidueDial_Core

/-!
# Batteries of residue dials: CRT composition and the bit-currency separation

A *battery* is a family of residue dials on pairwise coprime moduli, read
simultaneously.  The Chinese Remainder Theorem says that the joint filter on the
product modulus is exactly the "AND" of the individual filters
(`mem_crtDial`), and that its density is the *product* of the individual
densities (`crtDial_density`).

Two consequences are proved here.

* **The battery cap is still `4/3`** (`crtDial_speedup_le_four_thirds`,
  `batteryDensity_speedup_le_four_thirds`): composing dials — any number of
  them, on any moduli — cannot beat a single dial.  Composition is *free* in the
  sense that it costs nothing and buys nothing beyond the universal cap.

* **Capacity bits and work bits are different currencies.**  A battery of `n`
  half-density dials advertises `n` bits of capacity
  (`capacityBits_half_pow`), yet the work it buys is
  `workBits ≤ logb 2 (4/3) < 1` bit (`workBits_le_cap`, `workBits_lt_one`),
  and in fact tends to `0` as the capacity grows
  (`workBits_tendsto_zero_of_capacity_atTop`).  So the measured "battery bits"
  of a residue battery cannot be converted into work bits at par: capacity is
  unbounded while work is capped at `logb 2 (4/3)`.
-/

open ResidueDial

open Finset

/-! ## CRT composition of two dials -/

theorem ResidueDial.crtDial_density{m n : ℕ} [NeZero m] [NeZero n] (h : Nat.Coprime m n)
    (K₁ : Finset (ZMod m)ˣ) (K₂ : Finset (ZMod n)ˣ) :
    density (m * n) (crtDial h K₁ K₂) = density m K₁ * density n K₂ := by sorry
