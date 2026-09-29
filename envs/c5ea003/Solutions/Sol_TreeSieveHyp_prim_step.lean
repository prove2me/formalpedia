-- Prove2me | solution 1 for TreeSieveHyp.prim_step
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:19:05.636263+00:00
-- url     : https://prove2.me/submissions/40b796f2-cba2-43a0-9e3f-6f1b3efb30a6

-- Sol generated from Bridges/TreeSieveHypotenuseFace.lean
import Mathlib
import Definitions.Def_Bridges_TreeSieveHypotenuseFace
import Definitions.Def_Bridges_TreeSieveLottery
import Theorems.Thm_TreeSieve_step_pyth

/-!
# The hypotenuse face of the Berggren tree is blind to `3 mod 4` primes

The tree-sieve experiments measured a real but modest smoothness advantage of
Berggren-tree values over random integers (`7.31×`, against a naive `~44×`
prediction).  This file identifies the exact arithmetic reason — and shows that
the same structure is a *fatal* restriction for factoring.

Every node of the Berggren tree is a **primitive** Pythagorean triple
(`bergOf_prim`), and every prime divisor of the hypotenuse of a primitive triple
is `≡ 1 mod 4` (`prime_dvd_hyp_one_mod_four`).  So the hypotenuse values of the
tree are supported on the half of the primes congruent to `1 mod 4`: that is
where the observed smoothness boost comes from (the effective factor base is a
density-`1/2` subset of the primes, and hypotenuse values are never divisible by
`2, 3, 7, 11, 19, 23, …`).

The price is `hypotenuse_face_blind_to_three_mod_four`: for a modulus `N` all of
whose prime factors are `≡ 3 mod 4` — for example `N = p * q` with
`p ≡ q ≡ 3 mod 4` — the gcd of *any* tree hypotenuse with `N` is `1`.  The
lottery of `Catalog.Bridges.TreeSieveLottery` does not merely have a small
winning probability on this class of moduli: it has **no winning tickets at
all**, uniformly over the whole infinite tree.

Main results:

* `bergOf_prim` — every tree node is a primitive triple.
* `prime_dvd_hyp_one_mod_four` — prime divisors of hypotenuses of primitive
  triples are `1 mod 4`.
* `berg_hyp_prime_one_mod_four` — the same for every node of the tree.
* `hypotenuse_face_blind_to_three_mod_four` — zero success probability on
  `3 mod 4` moduli.
* `hypotenuse_face_blind_semiprime` — the concrete semiprime corollary.
-/

open TreeSieveHyp

open TreeSieve

/-! ## Primitivity is a tree invariant -/



/-- A prime dividing both legs of a Pythagorean triple divides the hypotenuse. -/
theorem prime_dvd_hyp_of_dvd_legs {a b c : ℤ} (hpy : a ^ 2 + b ^ 2 = c ^ 2) {r : ℕ}
    (hr : r.Prime) (ha : (r : ℤ) ∣ a) (hb : (r : ℤ) ∣ b) : (r : ℤ) ∣ c := by
  have hrp : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hr
  have : (r : ℤ) ∣ c ^ 2 := by
    rw [← hpy]
    exact dvd_add (Dvd.dvd.pow ha (by norm_num)) (Dvd.dvd.pow hb (by norm_num))
  exact hrp.dvd_of_dvd_pow this




/-! ## Prime divisors of a primitive hypotenuse are `1 mod 4` -/




/-! ## Consequence: zero winning tickets on `3 mod 4` moduli -/





/-! ## Sharpness: the obstruction is specific to the hypotenuse face -/




open TreeSieveHyp in
theorem solution(i : Fin 3) {t : Triple} (hpy : t.1 ^ 2 + t.2.1 ^ 2 = t.2.2 ^ 2)
    (h : Prim t) : Prim (step i t) := by
  obtain ⟨a, b, c⟩ := t
  intro r hr hdvd
  obtain ⟨ha', hb'⟩ := hdvd
  have hpy' := step_pyth i (a, b, c) hpy
  have hc' : (r : ℤ) ∣ (step i (a, b, c)).2.2 := prime_dvd_hyp_of_dvd_legs hpy' hr ha' hb'
  refine h r hr ⟨?_, ?_⟩ <;>
    fin_cases i <;> simp only [step] at ha' hb' hc' ⊢ <;>
    · obtain ⟨u, hu⟩ := ha'
      obtain ⟨v, hv⟩ := hb'
      obtain ⟨w, hw⟩ := hc'
      first
        | exact ⟨u + 2 * v - 2 * w, by linarith⟩
        | exact ⟨-2 * u - v + 2 * w, by linarith⟩
        | exact ⟨2 * u + v - 2 * w, by linarith⟩
        | exact ⟨-u - 2 * v + 2 * w, by linarith⟩
