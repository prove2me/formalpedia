-- Prove2me | solution 1 for GCDMoment.no_collision_le_three_of_pairSeparating
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:35:59.152387+00:00
-- url     : https://prove2.me/submissions/dcff899b-54c7-4845-ab1e-ed43a4c66331

-- Sol generated from Novelty/GCDMomentOmegaThree.lean
import Mathlib
import Definitions.Def_Novelty_GCDMomentHigherInversion
import Definitions.Def_Novelty_GCDMomentMultiplicative
import Definitions.Def_Novelty_GCDMomentPairInversion
import Definitions.Def_Novelty_GCDMomentRefinementOrder
import Definitions.Def_Novelty_GCDMomentTraceWitness
import Theorems.Thm_GCDMoment_all_prime_of_cardFactors_le_length
import Theorems.Thm_GCDMoment_collision_of_all_prime
import Theorems.Thm_GCDMoment_collision_of_singleton
import Theorems.Thm_GCDMoment_length_le_cardFactors

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
theorem solution{k : ℕ} (hk : 1 ≤ k)
    (hpair : ∀ {a b c d : ℕ}, 2 ≤ a → 2 ≤ b → 2 ≤ c → 2 ≤ d → a * b = c * d →
      factorisationEuler k [a, b] = factorisationEuler k [c, d] → ([a, b] : List ℕ).Perm [c, d])
    {n : ℕ} (hn : 2 ≤ n) (hOmega : cardFactors n ≤ 3) {l m : List ℕ} (h2l : ∀ a ∈ l, 2 ≤ a)
    (h2m : ∀ a ∈ m, 2 ≤ a) (hl : l.prod = n) (hm : m.prod = n)
    (heq : factorisationEuler k l = factorisationEuler k m) : l.Perm m := by
  have hlen_l : l.length ≤ 3 := by
    have := length_le_cardFactors l h2l; rw [hl] at this; omega
  have hlen_m : m.length ≤ 3 := by
    have := length_le_cardFactors m h2m; rw [hm] at this; omega
  have hl0 : l ≠ [] := by intro h; rw [h] at hl; simp at hl; omega
  have hm0 : m ≠ [] := by intro h; rw [h] at hm; simp at hm; omega
  have hprodeq : l.prod = m.prod := by rw [hl, hm]
  -- a three-part factorisation of a modulus with `Ω ≤ 3` consists of primes
  have hthree : ∀ (r : List ℕ), (∀ a ∈ r, 2 ≤ a) → r.prod = n → r.length = 3 →
      ∀ a ∈ r, a.Prime := by
    intro r h2r hrp hlen3
    refine all_prime_of_cardFactors_le_length r h2r ?_
    rw [hrp, hlen3]; omega
  by_cases hl3 : l.length = 3
  · exact collision_of_all_prime hk h2m (hthree l h2l hl hl3) hprodeq heq
  by_cases hm3 : m.length = 3
  · exact (collision_of_all_prime hk h2l (hthree m h2m hm hm3) hprodeq.symm heq.symm).symm
  -- otherwise both factorisations have one or two parts
  by_cases hl1 : l.length = 1
  · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hl1
    have han : a = n := by simpa using hl
    subst han
    rw [collision_of_singleton hk hn h2m hm heq]
  by_cases hm1 : m.length = 1
  · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hm1
    have han : a = n := by simpa using hm
    subst han
    rw [collision_of_singleton hk hn h2l hl heq.symm]
  have hl2 : l.length = 2 := by
    have : 1 ≤ l.length := List.length_pos_iff.2 hl0
    omega
  have hm2 : m.length = 2 := by
    have : 1 ≤ m.length := List.length_pos_iff.2 hm0
    omega
  obtain ⟨a, b, rfl⟩ : ∃ a b, l = [a, b] := by
    match l, hl2 with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  obtain ⟨c, d, rfl⟩ : ∃ c d, m = [c, d] := by
    match m, hm2 with
    | [c, d], _ => exact ⟨c, d, rfl⟩
  have hprod : a * b = c * d := by
    have := hprodeq; simpa using this
  exact hpair (h2l a (by simp)) (h2l b (by simp)) (h2m c (by simp)) (h2m d (by simp)) hprod heq
