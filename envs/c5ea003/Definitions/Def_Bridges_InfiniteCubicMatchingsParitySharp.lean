-- Prove2me | Definitions.Def_Bridges_InfiniteCubicMatchingsParitySharp
-- name    : Bridges_InfiniteCubicMatchingsParitySharp
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:28:14.288283+00:00
-- url     : https://prove2.me/theorems/e79294b1-22c8-4e36-b5c5-980583c6246c
-- title:
--   Aether Catalog definitions — Bridges_InfiniteCubicMatchingsParitySharp
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.InfiniteCubicMatchingsParitySharp`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/InfiniteCubicMatchingsParitySharp.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsLadder
/-
# Sharpness of the parity lemma in the infinite setting

The parity lemma `PerfectMatching.card_inter_cutEdges_odd` says that a perfect matching meets
every edge cut of odd size **with a finite side** in an odd number of edges.  In finite graphs
the finiteness assumption is vacuous.  Here we prove that in infinite graphs it cannot be
dropped: the infinite ladder has an edge cut of size `3` (odd), both sides of which are
infinite, that is *disjoint* from a perfect matching.

This is the fundamental new phenomenon of the infinite theory: parity arguments are only
available for cuts with a finite side, which is why `IsOddCut` is defined via a `Finset`.
-/

namespace Bridges.InfiniteCubicMatchings

namespace Ladder

/-- The vertex set consisting of all columns `≤ 0` together with the single extra vertex
`(1, false)`.  Both this set and its complement are infinite, and its edge cut has three
edges. -/
def leftPlus : Set (ℤ × Bool) := {p | p.1 ≤ 0 ∨ p = (1, false)}

/-- The partner map of the "shifted rails" matching: bottom vertices use the rails leaving
even columns, top vertices use the rails leaving odd columns. -/
def shiftedPartner : ℤ × Bool → ℤ × Bool
  | (n, false) => if n % 2 = 0 then (n + 1, false) else (n - 1, false)
  | (n, true) => if n % 2 = 0 then (n - 1, true) else (n + 1, true)

/-- The perfect matching of the ladder using the "even" rails on the bottom rail and the
"odd" rails on the top rail. -/
def shifted : PerfectMatching ladder where
  partner := shiftedPartner
  isAdj p := by
    obtain ⟨n, b⟩ := p
    cases b
    · by_cases h : n % 2 = 0
      · simp only [shiftedPartner, if_pos h]
        exact adj_rail n false
      · simp only [shiftedPartner, if_neg h]
        simpa using (adj_rail (n - 1) false).symm
    · by_cases h : n % 2 = 0
      · simp only [shiftedPartner, if_pos h]
        simpa using (adj_rail (n - 1) true).symm
      · simp only [shiftedPartner, if_neg h]
        exact adj_rail n true
  invol p := by
    obtain ⟨n, b⟩ := p
    cases b
    · by_cases h : n % 2 = 0
      · simp only [shiftedPartner, if_pos h]
        rw [if_neg (show ¬ ((n + 1) % 2 = 0) by omega)]
        simp
      · simp only [shiftedPartner, if_neg h]
        rw [if_pos (show (n - 1) % 2 = 0 by omega)]
        simp
    · by_cases h : n % 2 = 0
      · simp only [shiftedPartner, if_pos h]
        rw [if_neg (show ¬ ((n - 1) % 2 = 0) by omega)]
        simp
      · simp only [shiftedPartner, if_neg h]
        rw [if_pos (show (n + 1) % 2 = 0 by omega)]
        simp







end Ladder

end Bridges.InfiniteCubicMatchings


