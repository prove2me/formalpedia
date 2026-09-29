-- Prove2me | Theorems.Thm_FactoringBarriers_arithmetic_trajectory_blind
-- name    : FactoringBarriers.arithmetic_trajectory_blind
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:50:07.372539+00:00
-- url     : https://prove2.me/theorems/c8d43a5c-f98b-4011-8d79-16247bb7dcb5
-- title:
--   A blind trajectory.
-- statement:
--   **A blind trajectory.** The arithmetic trajectory `x_i = i` produces no
--   factor of `N = pq` from any pair of its first `min p q` points. Hence collision
--   based methods admit no worst-case guarantee below `min p q`, which for a
--   balanced semiprime is of order `√N` — not `N^{1/4}`.
--
--   ```lean
--   theorem FactoringBarriers.arithmetic_trajectory_blind{p q : ℕ} (hp : p.Prime) (hq : q.Prime)
--       {K : ℕ} (hKp : K ≤ p) (hKq : K ≤ q) (i j : Fin K) (hij : i ≠ j) :
--       Int.gcd ((i : ℤ) - (j : ℤ)) ((p * q : ℕ) : ℤ) = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/FactoringBarriers/RandomnessBarrier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/FactoringBarriers/RandomnessBarrier.lean#L58

-- Thm stub generated from Cryptography/FactoringBarriers/RandomnessBarrier.lean
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

theorem FactoringBarriers.arithmetic_trajectory_blind{p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {K : ℕ} (hKp : K ≤ p) (hKq : K ≤ q) (i j : Fin K) (hij : i ≠ j) :
    Int.gcd ((i : ℤ) - (j : ℤ)) ((p * q : ℕ) : ℤ) = 1 := by sorry
