-- Prove2me | Definitions.Def_Shared_MoonshineJWindow
-- name    : Shared_MoonshineJWindow
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:05:11.787256+00:00
-- url     : https://prove2.me/theorems/b3c9809c-fbc5-4902-80cc-f2e7b11df90b
-- title:
--   Aether Catalog definitions — Shared_MoonshineJWindow
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.MoonshineJWindow`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/MoonshineJWindow.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_MoonshineJExpansion

/-!
# Widening the verified window of the `j`-expansion

Third research cycle.  `Shared.MoonshineJExpansion` verified the head of the
`q`-expansion of `j = E₄³/Δ` to eight terms.  This file widens the kernel-checked
window to twelve terms and abstracts the uniqueness argument, so that the window
can be widened again by changing two numerals.

* `MoonshineJWindow.agree_of_deltaPart_mul` — **uniqueness at an arbitrary
  window**: two power series whose products with (possibly differently
  truncated) eta products both reproduce `E₄³` modulo `q^N` agree modulo `q^N`.
  This replaces the ad-hoc `N = 8` argument by a statement that scales.
* `MoonshineJWindow.E4_cube_agree_delta_mul_j12` — the verified identity
  `E₄³ ≡ (∏_{k≤11}(1-q^k)^24) · J₁₂ (mod q¹²)`.
* `MoonshineJWindow.j_coefficients_window` — consequently *every* solution of
  `Δ/q · f = E₄³` has the twelve tabulated coefficients, extending the moonshine
  head data to `c(10) = 22567393309593600`.
* `MoonshineJWindow.tau_values_twelve` — the first twelve Ramanujan tau values,
  and `tau_hecke_nine`, `tau_hecke_ten`, `tau_hecke_twelve` the Hecke relations
  `τ(9) = τ(3)² - 3¹¹`, `τ(10) = τ(2)τ(5)`, `τ(12) = τ(3)τ(4)` on them.
* `MoonshineJWindow.mckay_level_6` — the McKay decomposition of `c(6)`.
-/

namespace MoonshineJWindow

open Finset PowerSeries MoonshineJ

/-! ## 1. Uniqueness at an arbitrary window -/


/-! ## 2. The twelve-term window -/

/-- The tabulated head of `q · j` to twelve terms. -/
def jT12 : List ℤ :=
  [1, 744, 196884, 21493760, 864299970, 20245856256, 333202640600, 4252023300096,
   44656994071935, 401490886656000, 3176440229784420, 22567393309593600]

/-- The tabulated Ramanujan tau values `τ(1), …, τ(12)`. -/
def tauT12 : List ℤ :=
  [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612, -370944]



/-- The power series attached to the twelve-term table. -/
noncomputable def jSeries12 : PowerSeries ℤ := ser jT12




/-! ## 3. Tau values and Hecke relations on the wider window -/







/-! ## 4. One more McKay level -/


end MoonshineJWindow


