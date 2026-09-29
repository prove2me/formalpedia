-- Prove2me | Definitions.Def_Bridges_InfiniteCubicMatchingsLadder
-- name    : Bridges_InfiniteCubicMatchingsLadder
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:27:19.318893+00:00
-- url     : https://prove2.me/theorems/1a9cc2f7-8ecd-4a14-a4d3-5f9195715c9e
-- title:
--   Aether Catalog definitions — Bridges_InfiniteCubicMatchingsLadder
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.InfiniteCubicMatchingsLadder`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/InfiniteCubicMatchingsLadder.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
/-
# A concrete infinite cubic bridgeless graph satisfying all three conjectures

The doubly infinite ladder `L` on the vertex set `ℤ × Bool` (rungs `(n,b) — (n,¬b)` and rails
`(n,b) — (n+1,b)`) is an infinite, cubic, bridgeless graph.  We verify all of this formally
and exhibit an explicit proper 3-edge-colouring, which by
`ProperThreeEdgeColoring.bergeFulkerson` yields the Berge–Fulkerson property, hence also the
Fan–Raspaud and Máčajová–Škoviera properties.

This shows that the framework of `Bridges.InfiniteCubicMatchings` is not vacuous: it is
satisfied by a genuinely infinite cubic bridgeless graph.
-/

namespace Bridges.InfiniteCubicMatchings

namespace Ladder

/-- The doubly infinite ladder graph on `ℤ × Bool`. -/
def ladder : SimpleGraph (ℤ × Bool) where
  Adj p q := (p.1 = q.1 ∧ p.2 ≠ q.2) ∨ (p.2 = q.2 ∧ (q.1 = p.1 + 1 ∨ p.1 = q.1 + 1))
  symm := by
    rintro ⟨n, b⟩ ⟨m, c⟩ (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h1.symm, h2.symm⟩
  loopless := ⟨by
    rintro ⟨n, b⟩ (⟨-, h⟩ | ⟨-, h | h⟩)
    · exact h rfl
    · omega
    · omega⟩

lemma adj_rung (n : ℤ) (b : Bool) : ladder.Adj (n, b) (n, !b) := by
  refine Or.inl ⟨rfl, ?_⟩
  cases b <;> simp

lemma adj_rail (n : ℤ) (b : Bool) : ladder.Adj (n, b) (n + 1, b) := Or.inr ⟨rfl, Or.inl rfl⟩

/-! ## Three perfect matchings forming a proper 3-edge-colouring -/

/-- The matching consisting of all rungs. -/
def rung : PerfectMatching ladder where
  partner p := (p.1, !p.2)
  isAdj p := adj_rung p.1 p.2
  invol p := by simp

/-- The matching consisting of the rails leaving even columns to the right. -/
def evenRail : PerfectMatching ladder where
  partner p := if p.1 % 2 = 0 then (p.1 + 1, p.2) else (p.1 - 1, p.2)
  isAdj p := by
    by_cases h : p.1 % 2 = 0
    · simpa [h] using adj_rail p.1 p.2
    · simpa [h] using (adj_rail (p.1 - 1) p.2).symm
  invol p := by
    by_cases h : p.1 % 2 = 0
    · rw [if_pos h, if_neg (by simp; omega)]
      simp
    · rw [if_neg h, if_pos (by simp; omega)]
      simp

/-- The matching consisting of the rails leaving odd columns to the right. -/
def oddRail : PerfectMatching ladder where
  partner p := if p.1 % 2 = 0 then (p.1 - 1, p.2) else (p.1 + 1, p.2)
  isAdj p := by
    by_cases h : p.1 % 2 = 0
    · simpa [h] using (adj_rail (p.1 - 1) p.2).symm
    · simpa [h] using adj_rail p.1 p.2
  invol p := by
    by_cases h : p.1 % 2 = 0
    · rw [if_pos h, if_neg (by simp; omega)]
      simp
    · rw [if_neg h, if_pos (by simp; omega)]
      simp








/-! ## The ladder is an infinite, cubic, bridgeless graph -/









end Ladder

end Bridges.InfiniteCubicMatchings


