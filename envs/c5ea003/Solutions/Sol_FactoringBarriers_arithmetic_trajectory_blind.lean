-- Prove2me | solution 1 for FactoringBarriers.arithmetic_trajectory_blind
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:36:14.158772+00:00
-- url     : https://prove2.me/submissions/8266b729-63a0-4b2d-a059-aecac029f544

-- Sol generated from Cryptography/FactoringBarriers/RandomnessBarrier.lean
import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_CongruenceOfSquares
import Theorems.Thm_FactoringBarriers_gcd_eq_one_of_no_collision

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
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {K : ℕ} (hKp : K ≤ p) (hKq : K ≤ q) (i j : Fin K) (hij : i ≠ j) :
    Int.gcd ((i : ℤ) - (j : ℤ)) ((p * q : ℕ) : ℤ) = 1 := by
  have hne : (i : ℤ) - (j : ℤ) ≠ 0 := by
    intro h
    apply hij
    have : (i : ℤ) = (j : ℤ) := by linarith
    have : (i : ℕ) = (j : ℕ) := by exact_mod_cast this
    exact Fin.ext this
  have hlt : |(i : ℤ) - (j : ℤ)| < (K : ℤ) := by
    have hi : (i : ℤ) < (K : ℤ) := by exact_mod_cast i.isLt
    have hj : (j : ℤ) < (K : ℤ) := by exact_mod_cast j.isLt
    have hi0 : (0:ℤ) ≤ (i : ℤ) := by positivity
    have hj0 : (0:ℤ) ≤ (j : ℤ) := by positivity
    rw [abs_lt]; constructor <;> linarith
  refine gcd_eq_one_of_no_collision hp hq ?_ ?_
  · intro hdvd
    have := Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hdvd)
    have : (p : ℤ) ≤ (K : ℤ) - 1 := by omega
    have : (K : ℤ) ≤ (p : ℤ) := by exact_mod_cast hKp
    omega
  · intro hdvd
    have := Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hdvd)
    have : (q : ℤ) ≤ (K : ℤ) - 1 := by omega
    have : (K : ℤ) ≤ (q : ℤ) := by exact_mod_cast hKq
    omega
