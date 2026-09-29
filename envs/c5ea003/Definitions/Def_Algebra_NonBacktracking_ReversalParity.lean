-- Prove2me | Definitions.Def_Algebra_NonBacktracking_ReversalParity
-- name    : Algebra_NonBacktracking_ReversalParity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:26:32.939438+00:00
-- url     : https://prove2.me/theorems/eb1a1079-c82f-4745-a922-291288b05137
-- title:
--   Aether Catalog definitions — Algebra_NonBacktracking_ReversalParity
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.NonBacktracking.ReversalParity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/NonBacktracking/ReversalParity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace

/-!
# Reversal of non-backtracking walks and parity of the trace

Reversing a walk and flipping each of its darts is an involution on the set of rooted
closed non-backtracking walks. It has **no fixed point**: the root of the reversed walk
is the reversal of the root, and a dart is never equal to its own reversal. Consequently

`trace (B ^ n)` is even for every `n`.

For `n = 0` this recovers the classical handshake statement (the number of darts is even);
for `n ≥ 1` it says that closed non-backtracking walks come in genuinely distinct
clockwise/anticlockwise pairs.

## Main results

* `Hashimoto.even_card_of_involution` — a finset carrying a fixed-point-free involution
  has even cardinality (proved by summing the constant `1` over `ZMod 2`).
* `Hashimoto.revWalk_mem` — reversal preserves rooted closed non-backtracking walks.
* `Hashimoto.even_trace_hashimoto_pow` — `Even (trace (B ^ n))`.
-/

open Finset SimpleGraph List

namespace Hashimoto

/-! ## A parity tool -/


/-! ## Reversal of dart walks -/

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Reversal of a dart walk: reverse the order and flip every dart. -/
def revWalk (l : List G.Dart) : List G.Dart := (l.map SimpleGraph.Dart.symm).reverse






/-! ## The reversal intertwiner -/

/-- Dart reversal as an equivalence of the dart type. -/
def dartSymmEquiv (G : SimpleGraph V) : G.Dart ≃ G.Dart where
  toFun := SimpleGraph.Dart.symm
  invFun := SimpleGraph.Dart.symm
  left_inv := SimpleGraph.Dart.symm_symm
  right_inv := SimpleGraph.Dart.symm_symm



end Hashimoto


