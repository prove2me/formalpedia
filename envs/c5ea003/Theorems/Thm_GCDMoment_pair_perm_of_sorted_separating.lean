-- Prove2me | Theorems.Thm_GCDMoment_pair_perm_of_sorted_separating
-- name    : GCDMoment.pair_perm_of_sorted_separating
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:57:56.357382+00:00
-- url     : https://prove2.me/theorems/ab82e4e4-d6ad-40cd-9595-fe9eb3100867
-- title:
--   Separation of *sorted* pairs upgrades to separation up to order.
-- statement:
--   Separation of *sorted* pairs upgrades to separation up to order.
--
--   ```lean
--   theorem GCDMoment.pair_perm_of_sorted_separating{k : ℕ}
--       (hsorted : ∀ {a b c d : ℕ}, 2 ≤ a → a ≤ b → 2 ≤ c → c ≤ d → a * b = c * d →
--         factorisationEuler k [a, b] = factorisationEuler k [c, d] → a = c ∧ b = d)
--       {a b c d : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) (hprod : a * b = c * d)
--       (heq : factorisationEuler k [a, b] = factorisationEuler k [c, d]) :
--       ([a, b] : List ℕ).Perm [c, d] := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/GCDMomentOmegaThree.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/GCDMomentOmegaThree.lean#L54

-- Thm stub generated from Novelty/GCDMomentOmegaThree.lean
import Mathlib
import Definitions.Def_Novelty_GCDMomentHigherInversion
import Definitions.Def_Novelty_GCDMomentMultiplicative
import Definitions.Def_Novelty_GCDMomentPairInversion
import Definitions.Def_Novelty_GCDMomentRefinementOrder
import Definitions.Def_Novelty_GCDMomentTraceWitness

/-!
# Three prime factors: the moment still determines the factorisation, at `k = 1` and at `k ≥ 3`

Fifth cycle of the gcd-moment project.  Cycle 4
(`Novelty.GCDMomentFactorisationLattice`) proved that no collision of predicted moments can
involve an *extremal* factorisation, hence that no collision at all exists when the modulus has
at most two prime factors, at **every** `k ≥ 1`.  That bound is sharp at `k = 2`: the collision
`2·14 = 4·7` lives at `N = 28`, where `Ω(N) = 3`.

Here we push one step further in the other parameter.  The only factorisations left unconstrained
by cycle 4 at `Ω(n) = 3` are the *two-part* ones, and those are governed by a pair-separation
statement, because `factorisationEuler` on a two-element list *is* `pairMoment`
(`pairMoment_eq_euler`).  Pair separation is available at `k ≥ 3`
(`pairMoment_injective_of_three_le_unconditional`, cycle 2) and, by the elementary
sum-and-product argument, also at `k = 1`.  Hence:

* `factorisationEuler_pair_cast` — the bridge `E_k([a,b]) = pairMoment k a b`.
* `pair_perm_of_sorted_separating` — sorted pair separation upgrades to separation up to order.
* `pair_collision` (`k ≥ 3`) and `pair_collision_first` (`k = 1`) — the two pair-separation
  inputs.
* `no_collision_le_three_of_pairSeparating` — **the structural theorem**: pair separation at a
  given `k` plus the cycle-4 uniqueness of the two extremes already forces injectivity of the
  predicted moment on *all* factorisations of any modulus with `Ω(n) ≤ 3`.
* `no_collision_of_cardFactors_le_three` (`k ≥ 3`) and
  `no_collision_first_moment_of_cardFactors_le_three` (`k = 1`) — the two instances.

Both restrictions are sharp in the available data: at `k = 2` the modulus `28` with `Ω = 3`
collides, and removing `Ω ≤ 3` is exactly what the general `r`-factor conjecture still has to do
(at `k = 1` the smallest collision is `234 = 2·9·13 = 3·3·26`, with `Ω = 4`).
-/

open GCDMoment

open ArithmeticFunction

theorem GCDMoment.pair_perm_of_sorted_separating{k : ℕ}
    (hsorted : ∀ {a b c d : ℕ}, 2 ≤ a → a ≤ b → 2 ≤ c → c ≤ d → a * b = c * d →
      factorisationEuler k [a, b] = factorisationEuler k [c, d] → a = c ∧ b = d)
    {a b c d : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) (hprod : a * b = c * d)
    (heq : factorisationEuler k [a, b] = factorisationEuler k [c, d]) :
    ([a, b] : List ℕ).Perm [c, d] := by sorry
