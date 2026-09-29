-- Prove2me | solution 1 for GCDMoment.factorisationEuler_lt_primeProd_of_mem_not_prime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:19:51.550067+00:00
-- url     : https://prove2.me/submissions/7a63e2c8-5c16-4de2-b786-02daaf6113d0

-- Sol generated from Novelty/GCDMomentFactorisationLattice.lean
import Mathlib
import Definitions.Def_Novelty_GCDMomentMultiplicative
import Definitions.Def_Novelty_GCDMomentPairInversion
import Definitions.Def_Novelty_GCDMomentRefinementOrder
import Definitions.Def_Novelty_GCDMomentTraceWitness
import Theorems.Thm_GCDMoment_factorisationEuler_le_primeProd
import Theorems.Thm_GCDMoment_gcdMoment_gt_local_of_not_prime
import Theorems.Thm_GCDMoment_gcdMoment_le_primeProd
import Theorems.Thm_GCDMoment_primeProd_mul
import Theorems.Thm_GCDMoment_primeProd_pos

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


/-- A local factor of a part `≥ 1` is at least `1`. -/
lemma one_le_part {a k : ℕ} (ha : 1 ≤ a) (hk : 1 ≤ k) : 1 ≤ a ^ k + a - 1 := by
  have : a ≤ a ^ k := Nat.le_self_pow (by omega) a
  omega

@[simp] lemma factorisationEuler_nil (k : ℕ) : factorisationEuler k [] = 1 := by
  simp [factorisationEuler]

lemma factorisationEuler_cons (k a : ℕ) (t : List ℕ) :
    factorisationEuler k (a :: t) = (a ^ k + a - 1) * factorisationEuler k t := by
  simp [factorisationEuler]

lemma factorisationEuler_append (k : ℕ) (s t : List ℕ) :
    factorisationEuler k (s ++ t) = factorisationEuler k s * factorisationEuler k t := by
  simp [factorisationEuler, List.map_append, List.prod_append]

lemma factorisationEuler_pos {k : ℕ} (hk : 1 ≤ k) :
    ∀ {l : List ℕ}, (∀ a ∈ l, 1 ≤ a) → 0 < factorisationEuler k l
  | [], _ => by simp
  | (a :: t), h => by
      have ha : 1 ≤ a := h a (by simp)
      have ih : 0 < factorisationEuler k t :=
        factorisationEuler_pos hk (fun x hx => h x (by simp [hx]))
      have := one_le_part (a := a) (k := k) ha hk
      rw [factorisationEuler_cons]
      exact Nat.mul_pos (by omega) ih

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
theorem solution{k : ℕ} (hk : 1 ≤ k) {l : List ℕ}
    (h2 : ∀ a ∈ l, 2 ≤ a) {a : ℕ} (ha : a ∈ l) (hap : ¬ a.Prime) :
    factorisationEuler k l < primeProd k l.prod := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
  have h2a : 2 ≤ a := h2 a (by simp)
  have hmem : ∀ x ∈ s ++ a :: t, 2 ≤ x := h2
  have h2s : ∀ x ∈ s, 2 ≤ x := fun x hx => hmem x (by simp [hx])
  have h2t : ∀ x ∈ t, 2 ≤ x := fun x hx => hmem x (by simp [hx])
  have hsp : 0 < s.prod := List.prod_pos (fun x hx => by have := h2s x hx; omega)
  have htp : 0 < t.prod := List.prod_pos (fun x hx => by have := h2t x hx; omega)
  -- the composite part is strictly below its own prime product
  have hstrict : a ^ k + a - 1 < primeProd k a := by
    have h1 := gcdMoment_gt_local_of_not_prime h2a hap hk
    have h2' := gcdMoment_le_primeProd hk (n := a) (by omega)
    omega
  have hs : factorisationEuler k s ≤ primeProd k s.prod :=
    factorisationEuler_le_primeProd hk s (fun x hx => by have := h2s x hx; omega)
  have ht : factorisationEuler k t ≤ primeProd k t.prod :=
    factorisationEuler_le_primeProd hk t (fun x hx => by have := h2t x hx; omega)
  have hsp' : 0 < factorisationEuler k s :=
    factorisationEuler_pos hk (fun x hx => by have := h2s x hx; omega)
  have htp' : 0 < factorisationEuler k t :=
    factorisationEuler_pos hk (fun x hx => by have := h2t x hx; omega)
  have hkey : factorisationEuler k s * ((a ^ k + a - 1) * factorisationEuler k t)
      < primeProd k s.prod * (primeProd k a * primeProd k t.prod) := by
    have h1 : (a ^ k + a - 1) * factorisationEuler k t < primeProd k a * primeProd k t.prod :=
      Nat.mul_lt_mul_of_lt_of_le hstrict ht (primeProd_pos t.prod k)
    exact Nat.mul_lt_mul_of_le_of_lt hs h1 (primeProd_pos s.prod k)
  have hprodeq : (s ++ a :: t).prod = s.prod * (a * t.prod) := by
    rw [List.prod_append, List.prod_cons]
  rw [factorisationEuler_append, factorisationEuler_cons, hprodeq,
    primeProd_mul hsp.ne' (by positivity) k, primeProd_mul (by omega) htp.ne' k]
  exact hkey
