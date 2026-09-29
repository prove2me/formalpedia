-- Prove2me | Theorems.Thm_FactorLocationBarriers_divisor_pair_straddles_corner
-- name    : FactorLocationBarriers.divisor_pair_straddles_corner
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:35:31.907872+00:00
-- url     : https://prove2.me/theorems/72f7dddb-8166-4f2d-afe0-2581c716a3cb
-- title:
--   Tropical corner of the divisor hyperbola.
-- statement:
--   **Tropical corner of the divisor hyperbola.** For any divisor `d` of `N > 0`,
--   the pair `(d, N/d)` straddles `√N`: the smaller member is at most `√N` and the
--   larger one is at least `√N`. In logarithmic coordinates this says that the
--   hyperbola `x ⊙ y = N` is the tropical line with corner at `√N`.
--
--   ```lean
--   theorem FactorLocationBarriers.divisor_pair_straddles_corner(N d : ℕ) (hN : N ≠ 0) (hd : d ∣ N) :
--       min d (N / d) ≤ Nat.sqrt N ∧ Nat.sqrt N ≤ max d (N / d) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/FactorLocationBarriers.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/FactorLocationBarriers.lean#L74

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

theorem FactorLocationBarriers.divisor_pair_straddles_corner(N d : ℕ) (hN : N ≠ 0) (hd : d ∣ N) :
    min d (N / d) ≤ Nat.sqrt N ∧ Nat.sqrt N ≤ max d (N / d) := by sorry
