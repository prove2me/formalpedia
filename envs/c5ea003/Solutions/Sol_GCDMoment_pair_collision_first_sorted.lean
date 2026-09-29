-- Prove2me | solution 1 for GCDMoment.pair_collision_first_sorted
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:45:07.9588+00:00
-- url     : https://prove2.me/submissions/3cf06c5f-0ba1-4ca6-a7dc-596a7c6ed0ed

-- Sol generated from Novelty/GCDMomentOmegaThree.lean
import Mathlib
import Definitions.Def_Novelty_GCDMomentHigherInversion
import Definitions.Def_Novelty_GCDMomentMultiplicative
import Definitions.Def_Novelty_GCDMomentPairInversion
import Definitions.Def_Novelty_GCDMomentRefinementOrder
import Definitions.Def_Novelty_GCDMomentTraceWitness
import Theorems.Thm_GCDMoment_pairMoment_eq_euler
import Theorems.Thm_GCDMoment_sum_prod_determines_pair

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

/-- The predicted moment of a two-part factorisation *is* `pairMoment`. -/
theorem factorisationEuler_pair_cast {a b k : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ((factorisationEuler k [a, b] : ℕ) : ℤ) = pairMoment k (a : ℤ) (b : ℤ) := by
  have h1 : 1 ≤ a ^ k + a := le_trans ha (Nat.le_add_left a _)
  have h2 : 1 ≤ b ^ k + b := le_trans hb (Nat.le_add_left b _)
  rw [pairMoment_eq_euler]
  simp only [factorisationEuler, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
  ring


/-! ### Pair separation at `k ≥ 3` -/



/-! ### Pair separation at `k = 1` -/



/-! ### From pair separation to all factorisations of a modulus with `Ω ≤ 3` -/




/-! ### Lab notes

`Ω(28) = 3` and the second moment collides there (`2·14 = 4·7`), so the `k ≥ 3` hypothesis of
`no_collision_of_cardFactors_le_three` cannot be dropped; the third moment already separates the
same pair.  The smallest first-moment collision, `234 = 2·9·13 = 3·3·26`, has `Ω = 4`, so the
`Ω ≤ 3` hypothesis of `no_collision_first_moment_of_cardFactors_le_three` cannot be dropped
either. -/

example : factorisationEuler 2 [2, 14] = factorisationEuler 2 [4, 7] := by decide

example : factorisationEuler 3 [2, 14] ≠ factorisationEuler 3 [4, 7] := by decide

example : factorisationEuler 3 [2, 18] ≠ factorisationEuler 3 [3, 12] := by decide

example : factorisationEuler 1 [2, 9, 13] = factorisationEuler 1 [3, 3, 26] := by decide

example : (2 * 9 * 13 : ℕ) = 3 * 3 * 26 := by decide


open GCDMoment in
theorem solution{a b c d : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hc : 2 ≤ c)
    (hcd : c ≤ d) (hprod : a * b = c * d)
    (heq : factorisationEuler 1 [a, b] = factorisationEuler 1 [c, d]) : a = c ∧ b = d := by
  have h1 := factorisationEuler_pair_cast (a := a) (b := b) (k := 1) (by omega) (by omega)
  have h2 := factorisationEuler_pair_cast (a := c) (b := d) (k := 1) (by omega) (by omega)
  have hZ : pairMoment 1 (a : ℤ) (b : ℤ) = pairMoment 1 (c : ℤ) (d : ℤ) := by
    rw [← h1, ← h2, heq]
  rw [pairMoment_eq_euler, pairMoment_eq_euler] at hZ
  have hprodZ : (a : ℤ) * b = (c : ℤ) * d := by exact_mod_cast hprod
  have hsumZ : (a : ℤ) + b = (c : ℤ) + d := by
    simp only [pow_one] at hZ
    nlinarith [hZ, hprodZ]
  have hsum : a + b = c + d := by exact_mod_cast hsumZ
  exact sum_prod_determines_pair hprod hsum hab hcd
