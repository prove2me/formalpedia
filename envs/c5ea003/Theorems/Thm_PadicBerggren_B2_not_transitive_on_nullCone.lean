-- Prove2me | Theorems.Thm_PadicBerggren_B2_not_transitive_on_nullCone
-- name    : PadicBerggren.B2_not_transitive_on_nullCone
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T21:51:26.876565+00:00
-- url     : https://prove2.me/theorems/34eb5b3b-dc7e-45e5-8cc7-c65b7ead6704
-- title:
--   The reduced Berggren dynamics is never ergodic.
-- statement:
--   **The reduced Berggren dynamics is never ergodic.**  For every odd prime the hyperbolic
--   generator fails to be transitive on the `p² − 1` nonzero null vectors mod `p`: no single orbit
--   can exhaust the null cone, because orbits have at most `p + 1` elements while the punctured
--   null cone has `p² − 1 = (p − 1)(p + 1)` elements.
--
--   ```lean
--   theorem PadicBerggren.B₂_not_transitive_on_nullCone(hp : p ≠ 2) (v : Fin 3 → ZMod p) :
--       ¬ (∀ w ∈ (nullConeFinset p).erase 0, ∃ n : ℕ, (B₂ (ZMod p)) ^ n *ᵥ v = w) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PadicBerggrenOrbits.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
--
--   Upload correction: only the declared theorem identifier was normalized from PadicBerggren.B₂_not_transitive_on_nullCone to PadicBerggren.B2_not_transitive_on_nullCone; mathematical statement unchanged.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PadicBerggrenOrbits.lean#L67

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

theorem PadicBerggren.B2_not_transitive_on_nullCone(hp : p ≠ 2) (v : Fin 3 → ZMod p) :
    ¬ (∀ w ∈ (nullConeFinset p).erase 0, ∃ n : ℕ, (B₂ (ZMod p)) ^ n *ᵥ v = w) := by sorry
