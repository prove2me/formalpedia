-- Prove2me | Theorems.Thm_GCDMoment_local_lt_factorisationEuler
-- name    : GCDMoment.local_lt_factorisationEuler
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:52:23.638585+00:00
-- url     : https://prove2.me/theorems/f1606c1d-5e54-4165-97ef-9a17ba50450a
-- title:
--   The trivial factorisation is the unique minimiser.
-- statement:
--   **The trivial factorisation is the unique minimiser.**  As soon as a factorisation has two
--   parts, its predicted moment strictly exceeds the local factor of the modulus.
--
--   ```lean
--   theorem GCDMoment.local_lt_factorisationEuler{k : ℕ} (hk : 1 ≤ k) (a : ℕ) (t : List ℕ) (hne : t ≠ [])
--       (h : ∀ x ∈ a :: t, 2 ≤ x) :
--       (a :: t).prod ^ k + (a :: t).prod - 1 < factorisationEuler k (a :: t) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/GCDMomentFactorisationLattice.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/GCDMomentFactorisationLattice.lean#L128

-- Thm stub generated from Novelty/GCDMomentFactorisationLattice.lean
import Mathlib
import Definitions.Def_Novelty_GCDMomentMultiplicative
import Definitions.Def_Novelty_GCDMomentPairInversion
import Definitions.Def_Novelty_GCDMomentRefinementOrder
import Definitions.Def_Novelty_GCDMomentTraceWitness

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

theorem GCDMoment.local_lt_factorisationEuler{k : ℕ} (hk : 1 ≤ k) (a : ℕ) (t : List ℕ) (hne : t ≠ [])
    (h : ∀ x ∈ a :: t, 2 ≤ x) :
    (a :: t).prod ^ k + (a :: t).prod - 1 < factorisationEuler k (a :: t) := by sorry
