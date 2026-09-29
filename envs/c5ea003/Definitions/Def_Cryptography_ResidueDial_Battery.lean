-- Prove2me | Definitions.Def_Cryptography_ResidueDial_Battery
-- name    : Cryptography_ResidueDial_Battery
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:22:50.168641+00:00
-- url     : https://prove2.me/theorems/1a5c4cfd-abc6-466f-870b-b836197e5411
-- title:
--   Aether Catalog definitions — Cryptography_ResidueDial_Battery
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.ResidueDial.Battery`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/ResidueDial/Battery.lean by skeleton subtraction
import Mathlib
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

namespace ResidueDial

open Finset

/-! ## CRT composition of two dials -/

/-- The CRT isomorphism on unit groups: `(ZMod (m*n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ`
for coprime `m`, `n`. -/
noncomputable def crtUnits {m n : ℕ} (h : Nat.Coprime m n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

open scoped Classical in
/-- The composed dial: the residues mod `m*n` whose two CRT readings pass the
respective filters. -/
noncomputable def crtDial {m n : ℕ} (h : Nat.Coprime m n)
    (K₁ : Finset (ZMod m)ˣ) (K₂ : Finset (ZMod n)ˣ) : Finset (ZMod (m * n))ˣ :=
  (K₁ ×ˢ K₂).image (crtUnits h).symm





/-! ## Batteries of arbitrarily many dials -/

/-- The density of a battery is the product of the densities of its dials. -/
def batteryDensity (θs : List ℝ) : ℝ := θs.prod








/-! ## Capacity bits versus work bits -/

/-- The *capacity* of a dial of density `θ`, in bits: `log₂ (1/θ)`, the amount
of information the filter reveals about the target class. -/
noncomputable def capacityBits (θ : ℝ) : ℝ := -Real.logb 2 θ

/-- The *work* a dial of density `θ` buys, in bits: `log₂ (Speedup θ)`. -/
noncomputable def workBits (θ : ℝ) : ℝ := Real.logb 2 (speedup θ)








end ResidueDial


