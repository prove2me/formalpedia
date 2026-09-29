-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_alexander_natDegree_map_zmod
-- name    : Bridges.AlexanderTorus.alexander_natDegree_map_zmod
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:18:18.106352+00:00
-- url     : https://prove2.me/theorems/4eb5cc32-9fb1-420d-86cf-cb03005c1042
-- title:
--   No degree is lost in the reduction: `A_N mod ℓ` still has degree `N − 1`.
-- statement:
--   No degree is lost in the reduction: `A_N mod ℓ` still has degree `N − 1`.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.alexander_natDegree_map_zmod{N : ℕ} (hN : Odd N) :
--       ((alexander N).map (Int.castRingHom (ZMod ℓ))).natDegree = N - 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlexanderKnotNumberBridgeXIII.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlexanderKnotNumberBridgeXIII.lean#L59

-- Thm stub generated from Bridges/AlexanderKnotNumberBridgeXIII.lean
import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeXII
/-
# The knot–number bridge XIII: reduction mod `ℓ`

Conjecture `D2` of `FUTURE_DIRECTIONS.md` proposes that the mod-`ℓ` factorisation of `A_N`
is the classical Frobenius-orbit count applied blockwise to the divisor product of cycle I.
This file proves the structural half of that conjecture — everything except the orbit count
itself, which is a statement about `Φ_m` over `𝔽_ℓ` alone and involves no knot theory:

* `Bridges.AlexanderTorus.alexander_map_eq_prod_cyclotomic` : the divisor product survives any
  base change, `A_N` maps to `∏_{d ∣ N, d > 1} Φ_{2d}` over every commutative ring;
* `Bridges.AlexanderTorus.alexander_separable_zmod` and
  `Bridges.AlexanderTorus.alexander_squarefree_zmod` : for a prime `ℓ ∤ 2N` the reduction
  `A_N mod ℓ` is separable, hence squarefree — no cyclotomic block collapses;
* `Bridges.AlexanderTorus.alexander_natDegree_map_zmod` : the reduction still has degree
  `N − 1`, i.e. no leading coefficient is lost;
* `Bridges.AlexanderTorus.isRelPrime_cyclotomic_zmod_of_ne` : distinct blocks `Φ_{2d}`,
  `Φ_{2e}` (`d ≠ e` nontrivial divisors of `N`) stay relatively prime mod `ℓ`.

Together these say: for `ℓ ∤ 2N` the mod-`ℓ` picture is still indexed by the divisor lattice
of `N`, with `τ(N) − 1` pairwise coprime squarefree blocks of degrees `φ(d)`; only the
*internal* splitting of each block depends on `ℓ`.
-/

open Bridges.AlexanderTorus

open Polynomial Finset



variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)]

theorem Bridges.AlexanderTorus.alexander_natDegree_map_zmod{N : ℕ} (hN : Odd N) :
    ((alexander N).map (Int.castRingHom (ZMod ℓ))).natDegree = N - 1 := by sorry
