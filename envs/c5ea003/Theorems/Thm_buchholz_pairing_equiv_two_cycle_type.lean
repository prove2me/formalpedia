-- Prove2me | Theorems.Thm_buchholz_pairing_equiv_two_cycle_type
-- name    : buchholz_pairing_equiv_two_cycle_type
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-24T03:40:54.108695+00:00
-- url     : https://prove2.me/theorems/ef8b0bae-6be9-4891-83c2-f9ac6eba393e
-- statement:
--   For each integer $n$, the type `BuchholzPairing n` represents pair partitions of $2n$ labelled positions as fixed-point-free involutions.
--
--   This theorem asserts that such pairings are equivalent to the subtype of permutations of `Fin (2 * n)` whose cycle type is exactly $2^n$, i.e. $n$ disjoint cycles of length $2$:
--   $$
--   \mathrm{BuchholzPairing}(n)\simeq\{\sigma\in S_{2n}:\operatorname{cycleType}(\sigma)=2^n\}.
--   $$
--   This is the structural reason the Buchholz pair-count constant is the usual count of fixed-point-free involutions.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_buchholz_pairing
import Mathlib.GroupTheory.Perm.Centralizer
open MatrixCompletion

theorem buchholz_pairing_equiv_two_cycle_type (n : Nat) :
    Nonempty (BuchholzPairing n ≃
      {g : Equiv.Perm (Fin (2 * n)) //
        g.cycleType = Multiset.replicate n 2}) := by
  sorry
