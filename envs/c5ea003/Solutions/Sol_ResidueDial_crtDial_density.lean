-- Prove2me | solution 1 for ResidueDial.crtDial_density
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:45:56.969211+00:00
-- url     : https://prove2.me/submissions/4d86983a-f596-47b7-ad0a-585a24bfc3dc

-- Sol generated from Cryptography/ResidueDial/Battery.lean
import Mathlib
import Definitions.Def_Cryptography_ResidueDial_Battery
import Definitions.Def_Cryptography_ResidueDial_Core
import Theorems.Thm_ResidueDial_totient_pos_of_neZero

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




open scoped Classical in
theorem crtDial_card {m n : ℕ} (h : Nat.Coprime m n)
    (K₁ : Finset (ZMod m)ˣ) (K₂ : Finset (ZMod n)ˣ) :
    (crtDial h K₁ K₂).card = K₁.card * K₂.card := by
  classical
  rw [crtDial, Finset.card_image_of_injective _ (crtUnits h).symm.injective,
    Finset.card_product]



/-! ## Batteries of arbitrarily many dials -/









/-! ## Capacity bits versus work bits -/











open ResidueDial in
theorem solution{m n : ℕ} [NeZero m] [NeZero n] (h : Nat.Coprime m n)
    (K₁ : Finset (ZMod m)ˣ) (K₂ : Finset (ZMod n)ˣ) :
    density (m * n) (crtDial h K₁ K₂) = density m K₁ * density n K₂ := by
  have hm : (0:ℝ) < (m.totient : ℝ) := by exact_mod_cast totient_pos_of_neZero m
  have hn : (0:ℝ) < (n.totient : ℝ) := by exact_mod_cast totient_pos_of_neZero n
  rw [density, density, density, crtDial_card, Nat.totient_mul h]
  push_cast
  field_simp
