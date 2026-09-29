-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_dvd_of_alexander_dvd
-- name    : Bridges.AlexanderTorus.dvd_of_alexander_dvd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:18:56.183968+00:00
-- url     : https://prove2.me/theorems/5b7b1e21-3626-4304-8df1-7cbe1e34532f
-- title:
--   Hard direction: `A_d ∣ A_M` forces `d ∣ M`.
-- statement:
--   Hard direction: `A_d ∣ A_M` forces `d ∣ M`.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.dvd_of_alexander_dvd{d M : ℕ} (hd : Odd d) (hM : Odd M) (hd1 : 1 < d) (hM1 : 1 < M)
--       (h : alexander d ∣ alexander M) : d ∣ M := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlexanderKnotNumberBridgeIII.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlexanderKnotNumberBridgeIII.lean#L59

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

theorem Bridges.AlexanderTorus.dvd_of_alexander_dvd{d M : ℕ} (hd : Odd d) (hM : Odd M) (hd1 : 1 < d) (hM1 : 1 < M)
    (h : alexander d ∣ alexander M) : d ∣ M := by sorry
