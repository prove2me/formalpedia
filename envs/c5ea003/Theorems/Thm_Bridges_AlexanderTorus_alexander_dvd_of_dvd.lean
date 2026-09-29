-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_alexander_dvd_of_dvd
-- name    : Bridges.AlexanderTorus.alexander_dvd_of_dvd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:19:11.433524+00:00
-- url     : https://prove2.me/theorems/be5132f3-7268-4f90-a4ff-3a206204cb00
-- title:
--   Easy direction: `d ∣ M` implies `A_d ∣ A_M`.
-- statement:
--   Easy direction: `d ∣ M` implies `A_d ∣ A_M`.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.alexander_dvd_of_dvd{d M : ℕ} (hM : Odd M) (hd1 : 1 < d) (hM1 : 1 < M)
--       (hdvd : d ∣ M) : alexander d ∣ alexander M := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlexanderKnotNumberBridgeIII.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlexanderKnotNumberBridgeIII.lean#L34

-- Thm stub generated from Bridges/AlexanderKnotNumberBridgeIII.lean
import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
/-
# The Knot–Number bridge, third cycle: divisibility, separability, duality

Three structural theorems about the Alexander polynomial `A_N` of the torus knot
`T(2,N)`, all consequences of the cyclotomic factorization proved in
`Bridges.AlexanderKnotNumberBridge`:

* `alexander_dvd_iff_dvd` : **the divisibility bridge**
  `A_d ∣ A_M ↔ d ∣ M` (odd `d, M > 1`).
  Divisibility of torus-knot Alexander polynomials is *exactly* divisibility of the
  knot parameters — the divisor lattice of `N` is faithfully encoded in the
  divisibility order of the polynomials.
* `alexander_separable_rat` / `alexander_squarefree_rat` : `A_N` is separable
  (hence squarefree) over `ℚ`: the `N-1` roots are pairwise distinct, so the
  Alexander module `ℚ[X]/(A_N)` is a product of `τ(N)-1` distinct cyclotomic fields.
* `alexander_reverse` : `A_N` is palindromic, `A_N.reverse = A_N`, the polynomial
  shadow of Poincaré duality for the knot complement.
-/

open Bridges.AlexanderTorus

open Polynomial Finset

/-! ## The divisibility bridge -/

theorem Bridges.AlexanderTorus.alexander_dvd_of_dvd{d M : ℕ} (hM : Odd M) (hd1 : 1 < d) (hM1 : 1 < M)
    (hdvd : d ∣ M) : alexander d ∣ alexander M := by sorry
