-- Prove2me | Definitions.Def_Tropical_JacobiSignedNonDial
-- name    : Tropical_JacobiSignedNonDial
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:33.302853+00:00
-- url     : https://prove2.me/theorems/4c9a3ebb-9916-4c1b-8728-a1e11f6a8abf
-- title:
--   Aether Catalog definitions — Tropical_JacobiSignedNonDial
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.JacobiSignedNonDial`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/JacobiSignedNonDial.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Tropical_JacobiSignedMultiplicative

/-!
# The Jacobi-signed circle count escapes the residue dial

The earlier character-weighted witnesses (CIRC, BQF, GSP) all collapsed to a *residue
dial*: their value was a function of `N mod 4` or `N mod 8`.  Here we prove, by exact
evaluation, that the Jacobi-signed count is **not** a residue dial, and that the Weil
floor of `JacobiSignedWeilFloorBound.lean` is nearly attained.

* `JacSign.WZ_eq_WN` : the abstract statistic equals the concrete range-sum, so all the
  numerical statements below are statements about `W` / `WZ` themselves.
* `JacSign.W_17`, `JacSign.W_41`, ... : exact values (`-2`, `-10`, `-14`, ...).
* `JacSign.not_residue_dial_prime` : there is **no** function `f` with `W p = f (p % 8)`
  for all primes `p`.  (`17 ≡ 41 ≡ 1 (mod 8)` but `W 17 = -2 ≠ -10 = W 41`.)
* `JacSign.not_residue_dial_modulus` : likewise at composite level
  (`21 ≡ 85 ≡ 5 (mod 8)` but `WZ 21 = 0 ≠ -4 = WZ 85`).
* `JacSign.weil_floor_near_attained` : `W 173 = 26` and `26² = 676 > 0.97 · (4 · 173)`,
  so the bound `W p ^ 2 ≤ 4 p` cannot be improved by any constant factor `< 0.977`.
* `JacSign.not_constant_on_primes_mod_four` : the statistic is not a dial mod 4 either.
-/

open Finset

namespace JacSign

/-- A directly computable form of the statistic. -/
def WN (n : ℕ) : ℤ := ∑ x ∈ Finset.range n, jacobiSym ((x : ℤ) * (1 - (x : ℤ) ^ 2)) n


instance fact_prime_5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance fact_prime_13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩
instance fact_prime_17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩
instance fact_prime_29 : Fact (Nat.Prime 29) := ⟨by norm_num⟩
instance fact_prime_41 : Fact (Nat.Prime 41) := ⟨by norm_num⟩
instance fact_prime_53 : Fact (Nat.Prime 53) := ⟨by norm_num⟩
instance fact_prime_173 : Fact (Nat.Prime 173) := ⟨by norm_num⟩


set_option maxRecDepth 100000















instance fact_prime_3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
instance fact_prime_7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩




end JacSign


