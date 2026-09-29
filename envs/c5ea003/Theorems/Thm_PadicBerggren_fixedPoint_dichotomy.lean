-- Prove2me | Theorems.Thm_PadicBerggren_fixedPoint_dichotomy
-- name    : PadicBerggren.fixedPoint_dichotomy
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:35:04.70885+00:00
-- url     : https://prove2.me/theorems/fa90782f-1be3-416c-a409-80ade38523a4
-- title:
--   Counting form of the spectral dichotomy.
-- statement:
--   **Counting form of the spectral dichotomy.**  Mod an odd prime the unipotent generator has
--   `p` fixed points (a whole isotropic line inside the null cone) while the hyperbolic generator
--   has exactly one (the origin).
--
--   ```lean
--   theorem PadicBerggren.fixedPoint_dichotomy(hp : p ≠ 2) :
--       ((univ : Finset (Fin 3 → ZMod p)).filter (fun w => B₁ (ZMod p) *ᵥ w = w)).card = p ∧
--       ((univ : Finset (Fin 3 → ZMod p)).filter (fun w => B₂ (ZMod p) *ᵥ w = w)).card = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PadicBerggrenOrbits.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PadicBerggrenOrbits.lean#L180

-- Thm stub generated from Geometry/PadicBerggrenOrbits.lean
import Mathlib
import Definitions.Def_Geometry_PadicBerggrenDynamics
import Definitions.Def_Geometry_PadicBerggrenNullCone

/-!
# Orbit structure of the reduced Berggren dynamics

Building on `Catalog/Geometry/PadicBerggrenDynamics.lean` (the three Berggren generators as a
dynamical system on `(ZMod (p^k))³`) and on `Catalog/Geometry/PadicBerggrenNullCone.lean`
(the phase space has exactly `p²` points), this file settles the **orbit structure** of the
generators on the null cone mod an odd prime.

## Main results

* `PadicBerggren.pow_mod_eq` : an elementary periodicity reduction, `M^n = M^(n % m)` whenever
  `M^m = 1`.
* `PadicBerggren.B₂_pow_le_p_add_one` : for every odd prime there is a period `m` with
  `1 ≤ m ≤ p + 1` and `B₂^m = 1` — either `p − 1` (split case, `2` a square mod `p`) or
  `p + 1` (inert case).  So the *actual* period of the hyperbolic generator is at most `p + 1`,
  much smaller than the a priori bound `p² − 1`.
* `PadicBerggren.B₂_orbit_card_le` : every `B₂`-orbit on `(ZMod p)³` has at most `p + 1` points.
* `PadicBerggren.B₂_not_transitive_on_nullCone` : consequently, for every odd prime the
  hyperbolic generator is **never transitive** on the `p² − 1` nonzero null vectors: the reduced
  Berggren dynamics is *never ergodic* on the null cone, and there are at least
  `(p² − 1)/(p + 1) = p − 1` distinct orbits.  This is the precise sense in which the p-adic
  picture differs from the real one, where the hyperbolic generator has dense orbits on the
  boundary.
* `PadicBerggren.card_B₁_fixedPoints` : the unipotent generator fixes exactly `p` points — a
  whole isotropic line — whereas `B₂` fixes only the origin (`B₂_no_nonzero_fixed_point`).
  This is the counting form of the unipotent/hyperbolic spectral dichotomy.
-/

open PadicBerggren

open Matrix Finset


variable (p : ℕ) [Fact p.Prime]




/-! ### The split case: an explicit null eigenvector and its exact period

When `2` is a square mod `p` (equivalently `p ≡ ±1 mod 8`) the hyperbolic generator has the
null eigenvector `(1,1,√2)` with eigenvalue `3 + 2√2`, the fundamental unit squared.  Its orbit
is therefore the geometric progression of the eigenvalue, and its exact period is the
multiplicative order of `3 + 2√2` in `(ZMod p)ˣ`. -/

theorem PadicBerggren.fixedPoint_dichotomy(hp : p ≠ 2) :
    ((univ : Finset (Fin 3 → ZMod p)).filter (fun w => B₁ (ZMod p) *ᵥ w = w)).card = p ∧
    ((univ : Finset (Fin 3 → ZMod p)).filter (fun w => B₂ (ZMod p) *ᵥ w = w)).card = 1 := by sorry
