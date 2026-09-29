-- Prove2me | Theorems.Thm_FactorLocationBarriers_energyGroundSet_ncard
-- name    : FactorLocationBarriers.energyGroundSet_ncard
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:35:56.317645+00:00
-- url     : https://prove2.me/theorems/0a3f6a2f-4363-4310-b467-abdea82081e8
-- title:
--   OPO-FAC / MPS-PARENT, closed (density).
-- statement:
--   **OPO-FAC / MPS-PARENT, closed (density).** The ground space has exactly four
--   points, independently of the size of `N`: random restarts over the `N²`-point
--   configuration space succeed with density `4/N²`, i.e. the analog resource does not
--   change the counting.
--
--   ```lean
--   theorem FactorLocationBarriers.energyGroundSet_ncard(p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hlt : p < q) :
--       {ab : ℕ × ℕ | energy (p * q) ab.1 ab.2 = 0}.ncard = 4 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/FactorLocationBarriers.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/FactorLocationBarriers.lean#L185

-- Thm stub generated from Tropical/FactorLocationBarriers.lean
import Mathlib
import Definitions.Def_Tropical_FactorLocationBarriers

/-!
# Counting is free, locating is hard: the semiprime witness barriers

This file formalises the arithmetic core of the round-4 closures `HOLOG-MARGIN`,
`SPARSEREC`, `MPS-PARENT` and `OPO-FAC`. All four hypotheses proposed an exotic
resource (holographic partition functions, compressed sensing, tensor-network
ground states, optical Ising machines) for factoring a semiprime `N = p q`, and
all four were closed by the same structural fact, which we prove here:

* the *counting* data attached to `N` (number of divisor pairs = partition
  function `Z = τ(N) = 4`) is **constant across all semiprimes**, hence carries
  zero information (`card_divisors_semiprime`, `tau_cannot_locate`);
* the *witness* data is a 2-spike vector: exactly two divisors lie in the search
  window `[1, √N]`, namely `1` and `p` (`divisors_below_corner`), so the search
  space that must be aggregated has size `√N` with exactly one nontrivial hit
  (`nontrivial_witness_below_corner`);
* the ground space of the tensor-network / Ising energy `E(a,b) = (N - ab)²` is
  the four-point divisor set `{(1,N),(p,q),(q,p),(N,1)}` with no intermediate
  structure (`energyGroundSet_eq`, `energyGroundSet_ncard`), so descent has no
  gradient and random search succeeds with density `4/N²`.

The min-plus (tropical) thread: in logarithmic coordinates the divisor hyperbola
`x · y = N` is the tropical line `X ⊙ Y = N`, whose corner is at `√N`; every
divisor pair straddles that corner (`divisor_pair_straddles_corner`). The
"free witness aggregation" barrier is precisely the statement that locating the
unique nontrivial lattice point on one side of the corner costs the whole
window.
-/

open FactorLocationBarriers

/-! ## 1. The divisor set of a semiprime -/




/-! ## 2. The tropical corner: every divisor pair straddles `√N` -/


/-! ## 3. SPARSEREC: the witness vector is a 2-spike -/




/-! ## 4. MPS-PARENT / OPO-FAC: the ground space is a four-point delta -/

theorem FactorLocationBarriers.energyGroundSet_ncard(p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hlt : p < q) :
    {ab : ℕ × ℕ | energy (p * q) ab.1 ab.2 = 0}.ncard = 4 := by sorry
