-- Prove2me | solution 1 for GCDMoment.no_collision_of_cardFactors_le_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:35:59.651844+00:00
-- url     : https://prove2.me/submissions/a827260a-5886-43eb-9426-48cd25b290eb

-- Sol generated from Novelty/GCDMomentFactorisationLattice.lean
import Mathlib
import Definitions.Def_Novelty_GCDMomentMultiplicative
import Definitions.Def_Novelty_GCDMomentPairInversion
import Definitions.Def_Novelty_GCDMomentRefinementOrder
import Definitions.Def_Novelty_GCDMomentTraceWitness
import Theorems.Thm_GCDMoment_all_prime_of_cardFactors_le_length
import Theorems.Thm_GCDMoment_collision_of_all_prime
import Theorems.Thm_GCDMoment_collision_of_singleton
import Theorems.Thm_GCDMoment_length_le_cardFactors

/-!
# The factorisation lattice of a gcd moment: both extremes are attained *uniquely*

This is the fourth cycle of the gcd-moment project
(`Novelty.GCDMomentTraceWitness`, `Novelty.GCDMomentPairInversion`,
`Novelty.GCDMomentHigherInversion`, `Novelty.GCDMomentMultiplicative`,
`Novelty.GCDMomentRefinementOrder`).

Cycle 3 proved that the moment predicted by *any* factorisation `n = a_1 ⋯ a_r` into parts
`a_i ≥ 2`, namely

`E_k(a_1,…,a_r) = ∏_i (a_i^k + a_i − 1)`  (`factorisationEuler`),

lies in the bracket `[n^k + n − 1, Π_k(n)]`, where `Π_k(n)` is the value at the prime
factorisation (`primeProd`).  What was missing was *uniqueness* at the two ends.  This file
supplies it and draws the consequence for the inversion problem:

* `factorisationEuler_all_prime` — a factorisation into primes always predicts `Π_k(n)`.
* `factorisationEuler_lt_primeProd_of_mem_not_prime` — one composite part already makes the
  prediction *strictly* smaller than `Π_k(n)`.
* `factorisationEuler_eq_primeProd_iff_all_prime` — **the prime factorisation is the unique
  maximiser** of the predicted moment.
* `local_le_factorisationEuler`, `local_lt_factorisationEuler` — the natural-number form of the
  lower end, with strictness as soon as there are two parts: **the trivial factorisation `[n]` is
  the unique minimiser.**
* `collision_of_all_prime`, `collision_of_singleton` — consequently *no* collision of predicted
  moments can involve an extremal factorisation: if two factorisations of the same modulus
  predict the same moment and one of them is the prime factorisation (resp. the trivial
  factorisation), they agree up to order.
* `length_le_cardFactors`, `all_prime_of_cardFactors_le_length` — the combinatorial input: a
  factorisation into parts `≥ 2` has at most `Ω(n)` parts, with equality exactly when every part
  is prime.
* `no_collision_of_cardFactors_le_two` — **the capstone**: for every `k ≥ 1`, if `Ω(n) ≤ 2` then
  the predicted moment determines the factorisation up to order.  In particular
  `no_collision_semiprime`: on the semiprime moduli that the factoring question is about, *every*
  moment — including the ambiguous `k = 2` — is injective on factorisations.  Every collision
  (e.g. the `k = 2` collisions `2·14 = 4·7` at `N = 28` and `2·18 = 3·12` at `N = 36`) therefore
  needs `Ω(N) ≥ 3` and a composite part on *both* sides, which is exactly what those two
  examples show.
-/

open GCDMoment

open ArithmeticFunction

/-! ### Arithmetic of the natural-number Euler product -/







/-! ### The lower end of the bracket, in `ℕ` -/




/-! ### The upper end of the bracket: uniqueness of the maximiser -/




/-! ### No collision can involve an extremal factorisation -/



/-! ### The combinatorics of the number of parts -/



/-! ### The capstone: at most two prime factors ⟹ no collision at any `k` -/



/-! ### Lab notes: the two known collisions really do have three prime factors

`28 = 2·14 = 4·7` and `36 = 2·18 = 3·12` are the complete list of second-moment collisions
(`Novelty.GCDMomentPairInversion`).  Both moduli have `Ω ≥ 3`, and on each side of each
collision one part is composite — exactly as `no_collision_of_cardFactors_le_two`,
`collision_of_all_prime` and `collision_of_singleton` require. -/

example : factorisationEuler 2 [2, 14] = factorisationEuler 2 [4, 7] := by decide

example : factorisationEuler 2 [2, 18] = factorisationEuler 2 [3, 12] := by decide

example : cardFactors 28 = 3 := by
  rw [show (28 : ℕ) = 2 * (2 * 7) by norm_num,
    cardFactors_mul (by norm_num) (by norm_num),
    cardFactors_mul (by norm_num) (by norm_num),
    cardFactors_eq_one_iff_prime.2 (by norm_num),
    cardFactors_eq_one_iff_prime.2 (by norm_num)]

example : cardFactors 36 = 4 := by
  rw [show (36 : ℕ) = 2 * (2 * (3 * 3)) by norm_num,
    cardFactors_mul (by norm_num) (by norm_num),
    cardFactors_mul (by norm_num) (by norm_num),
    cardFactors_mul (by norm_num) (by norm_num),
    cardFactors_eq_one_iff_prime.2 (by norm_num),
    cardFactors_eq_one_iff_prime.2 (by norm_num)]

/-- The prime factorisation of `28` beats both of its two-part factorisations, and the trivial
factorisation loses to both: the bracket of cycle 3 is strict at the ends. -/
example : factorisationEuler 2 [28] < factorisationEuler 2 [2, 14] ∧
    factorisationEuler 2 [2, 14] < factorisationEuler 2 [2, 2, 7] := by decide

/-- The four factorisations of `28` and their predicted second moments: the two extremes are
attained exactly once, the middle value twice. -/
example : factorisationEuler 2 [28] = 811 ∧ factorisationEuler 2 [2, 14] = 1045 ∧
    factorisationEuler 2 [4, 7] = 1045 ∧ factorisationEuler 2 [2, 2, 7] = 1375 := by decide


open GCDMoment in
theorem solution{k : ℕ} (hk : 1 ≤ k) {n : ℕ} (hn : 2 ≤ n)
    (hOmega : cardFactors n ≤ 2) {l m : List ℕ} (h2l : ∀ a ∈ l, 2 ≤ a) (h2m : ∀ a ∈ m, 2 ≤ a)
    (hl : l.prod = n) (hm : m.prod = n)
    (heq : factorisationEuler k l = factorisationEuler k m) : l.Perm m := by
  have hlen_l : l.length ≤ 2 := by
    have := length_le_cardFactors l h2l
    rw [hl] at this; omega
  have hlen_m : m.length ≤ 2 := by
    have := length_le_cardFactors m h2m
    rw [hm] at this; omega
  have hl0 : l ≠ [] := by
    intro h; rw [h] at hl; simp at hl; omega
  have hm0 : m ≠ [] := by
    intro h; rw [h] at hm; simp at hm; omega
  -- if either side has a single part, that part is `n` and the other side must match
  by_cases hl1 : l.length = 1
  · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hl1
    have : a = n := by simpa using hl
    subst this
    have := collision_of_singleton hk hn h2m hm heq
    rw [this]
  by_cases hm1 : m.length = 1
  · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hm1
    have : a = n := by simpa using hm
    subst this
    have := collision_of_singleton hk hn h2l hl heq.symm
    rw [this]
  -- otherwise both sides have exactly two parts, hence `Ω(n) = 2` and all parts are prime
  have hl2 : l.length = 2 := by
    have : 1 ≤ l.length := List.length_pos_iff.2 hl0
    omega
  have hm2 : m.length = 2 := by
    have : 1 ≤ m.length := List.length_pos_iff.2 hm0
    omega
  have hpl : ∀ a ∈ l, a.Prime := by
    refine all_prime_of_cardFactors_le_length l h2l ?_
    rw [hl, hl2]; omega
  exact collision_of_all_prime hk h2m hpl (by rw [hl, hm]) heq
