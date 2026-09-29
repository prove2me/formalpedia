-- Prove2me | solution 1 for GCDMoment.local_lt_factorisationEuler
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:26:28.73434+00:00
-- url     : https://prove2.me/submissions/ed195b5a-02e0-4660-8598-01c512f3f3a2

-- Sol generated from Novelty/GCDMomentFactorisationLattice.lean
import Mathlib
import Definitions.Def_Novelty_GCDMomentMultiplicative
import Definitions.Def_Novelty_GCDMomentPairInversion
import Definitions.Def_Novelty_GCDMomentRefinementOrder
import Definitions.Def_Novelty_GCDMomentTraceWitness
import Theorems.Thm_GCDMoment_local_le_factorisationEuler
import Theorems.Thm_GCDMoment_local_refine_nat

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

/-- A single local factor of a part `≥ 2` is at least `3`. -/
lemma three_le_part {a k : ℕ} (ha : 2 ≤ a) (hk : 1 ≤ k) : 3 ≤ a ^ k + a - 1 := by
  have : a ≤ a ^ k := Nat.le_self_pow (by omega) a
  omega



lemma factorisationEuler_cons (k a : ℕ) (t : List ℕ) :
    factorisationEuler k (a :: t) = (a ^ k + a - 1) * factorisationEuler k t := by
  simp [factorisationEuler]



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
theorem solution{k : ℕ} (hk : 1 ≤ k) (a : ℕ) (t : List ℕ) (hne : t ≠ [])
    (h : ∀ x ∈ a :: t, 2 ≤ x) :
    (a :: t).prod ^ k + (a :: t).prod - 1 < factorisationEuler k (a :: t) := by
  have ha : 2 ≤ a := h a (by simp)
  have hrest : 2 ≤ t.prod := by
    obtain ⟨b, s, rfl⟩ : ∃ b s, t = b :: s := by
      cases t with
      | nil => exact absurd rfl hne
      | cons b s => exact ⟨b, s, rfl⟩
    have hb : 2 ≤ b := h b (by simp)
    have : 1 ≤ s.prod := List.one_le_prod (fun x hx => by have := h x (by simp [hx]); omega)
    rw [List.prod_cons]
    calc 2 = 2 * 1 := by ring
      _ ≤ b * s.prod := Nat.mul_le_mul hb this
  have ih : t.prod ^ k + t.prod - 1 ≤ factorisationEuler k t :=
    local_le_factorisationEuler hk t hne (fun x hx => h x (by simp [hx]))
  have hstep := local_refine_nat ha hrest hk
  have hpos : 0 < a ^ k + a - 1 := by have := three_le_part ha hk; omega
  calc (a :: t).prod ^ k + (a :: t).prod - 1
      = (a * t.prod) ^ k + a * t.prod - 1 := by rw [List.prod_cons]
    _ < (a ^ k + a - 1) * (t.prod ^ k + t.prod - 1) := hstep
    _ ≤ (a ^ k + a - 1) * factorisationEuler k t := Nat.mul_le_mul_left _ ih
    _ = factorisationEuler k (a :: t) := (factorisationEuler_cons _ _ _).symm
