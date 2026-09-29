-- Prove2me | Theorems.Thm_buchholz_pairing_count_eq_two_cycle_type_card
-- name    : buchholz_pairing_count_eq_two_cycle_type_card
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-24T03:11:37.91616+00:00
-- url     : https://prove2.me/theorems/874c9504-5984-43fb-9e15-2b33273449c1
-- statement:
--   For each $n$, the type `BuchholzPairing n` consists of fixed-point-free involutions on the $2n$ labelled positions.
--
--   This theorem identifies its cardinality with the cardinality of the cycle-type class consisting of $n$ disjoint $2$-cycles:
--   $$
--   |\mathrm{BuchholzPairing}(n)|=\#\{\sigma\in S_{2n}:\operatorname{cycleType}(\sigma)=2^n\}.
--   $$
--   It is the structural bridge between pair partitions and Mathlib's permutation cycle-type counting theorem.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_buchholz_pairing
import Mathlib.GroupTheory.Perm.Centralizer
open MatrixCompletion

theorem buchholz_pairing_count_eq_two_cycle_type_card (n : Nat) :
    Fintype.card (BuchholzPairing n) =
      ({g | g.cycleType = Multiset.replicate n 2} :
        Finset (Equiv.Perm (Fin (2 * n)))).card := by
  sorry
