-- Prove2me | Definitions.Def_buchholz_pairing
-- name    : buchholz_pairing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-24T02:59:27.589604+00:00
-- url     : https://prove2.me/theorems/16daac9a-b49e-4521-a50c-7864c8dd5dc6
-- statement:
--   This definition introduces the pairing object used in the Buchholz form of the noncommutative Khintchine inequality.
--
--   For an integer $n$, `BuchholzPairing n` is the type of fixed-point-free involutions of the $2n$ labelled edge-occurrence positions. Equivalently, its elements are pair partitions of $\{1,\ldots,2n\}$: every position is matched with exactly one distinct partner, and applying the matching twice returns to the original position.
--
--   This is the combinatorial vocabulary needed to separate the matched-walk estimate from the elementary enumeration of pair partitions.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_buchholz_walk_sum
import Mathlib.GroupTheory.Perm.Basic

/-!
Pairing vocabulary for the Buchholz matched-walk estimate.

Buchholz's proof of the noncommutative Khintchine inequality controls the
matched closed-walk expansion by grouping the `2n` edge occurrences into
pairs.  A pair partition of `2n` labelled positions is represented here as a
fixed-point-free involution on `Fin (2 * n)`.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- A pair partition of the `2 * n` positions, represented as a fixed-point-free
involution.  Each orbit of the permutation has exactly two elements. -/
abbrev BuchholzPairing (n : Nat) :=
  {pair : Equiv.Perm (Fin (2 * n)) //
    Function.Involutive pair ∧ ∀ k : Fin (2 * n), pair k ≠ k}

noncomputable instance (n : Nat) : Fintype (BuchholzPairing n) := by
  classical
  unfold BuchholzPairing
  infer_instance

noncomputable instance (n : Nat) : DecidableEq (BuchholzPairing n) := by
  classical
  unfold BuchholzPairing
  infer_instance

end MatrixCompletion


