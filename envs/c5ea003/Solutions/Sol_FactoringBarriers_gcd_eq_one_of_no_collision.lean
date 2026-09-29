-- Prove2me | solution 1 for FactoringBarriers.gcd_eq_one_of_no_collision
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:35:03.745716+00:00
-- url     : https://prove2.me/submissions/af968129-17c3-433a-851e-63b56172851c

-- Sol generated from Cryptography/FactoringBarriers/RandomnessBarrier.lean
import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_CongruenceOfSquares

/-!
# The Randomness/Collision Barrier, Made Worst-Case Rigorous

Pollard's rho method and every other *collision-based* factoring method work by
computing `gcd(x_i - x_j, N)` for iterates of some map. The quoted running time
`Θ(N^{1/4})` is a **birthday heuristic**: it assumes the iterates behave like
uniform random residues modulo the unknown prime `p ≈ √N`.

This file proves the two unconditional facts that sit underneath that heuristic.

* `gcd_eq_one_of_no_collision` — a difference of iterates yields a nontrivial
  factor of `N = pq` **only if** the iterates collide modulo `p` or modulo `q`.
  So collision-finding is not one strategy among many for these methods: it is
  the whole method.
* `arithmetic_trajectory_blind` — the trajectory `x_i = i` is collision-free for
  the first `min p q` steps, hence produces *nothing*. Consequently no
  worst-case guarantee better than `min p q ≈ √N` is available for
  collision-based methods; the `N^{1/4}` figure is average-case only.

Both statements are honest sharpenings of "barrier 8": the barrier that is
actually provable in the worst case is `√N`, and the celebrated `N^{1/4}` is a
probabilistic phenomenon, not a theorem about all trajectories.
-/

open FactoringBarriers





open FactoringBarriers in
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) {a b : ℤ}
    (hpc : ¬ (p : ℤ) ∣ (a - b)) (hqc : ¬ (q : ℤ) ∣ (a - b)) :
    Int.gcd (a - b) ((p * q : ℕ) : ℤ) = 1 := by
  set d : ℕ := Int.gcd (a - b) ((p * q : ℕ) : ℤ) with hd
  by_contra hne
  have hdvdN : d ∣ p * q := by
    have : (d : ℤ) ∣ ((p * q : ℕ) : ℤ) := Int.gcd_dvd_right _ _
    exact_mod_cast this
  have hdvdab : (d : ℤ) ∣ (a - b) := Int.gcd_dvd_left _ _
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0] at hdvdN
    have := Nat.eq_zero_of_zero_dvd hdvdN
    have : p = 0 ∨ q = 0 := by
      rcases Nat.mul_eq_zero.mp this with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases this with h | h
    · exact hp.pos.ne' h
    · exact hq.pos.ne' h
  have hd1 : 1 < d := by omega
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
  have hrN : r ∣ p * q := hrd.trans hdvdN
  have hrab : (r : ℤ) ∣ (a - b) := dvd_trans (by exact_mod_cast hrd) hdvdab
  rcases (Nat.Prime.dvd_mul hr).mp hrN with h | h
  · exact hpc (by rw [(Nat.prime_dvd_prime_iff_eq hr hp).mp h] at hrab; exact hrab)
  · exact hqc (by rw [(Nat.prime_dvd_prime_iff_eq hr hq).mp h] at hrab; exact hrab)
