-- Prove2me | Theorems.Thm_EmergentGeometry_no_bulk_geometry_realises_Sw
-- name    : EmergentGeometry.no_bulk_geometry_realises_Sw
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:41:18.098756+00:00
-- url     : https://prove2.me/theorems/2395d420-1c83-467e-a867-e275b85545d6
-- title:
--   The witness vector is not holographic.
-- statement:
--   **The witness vector is not holographic.**  No bulk graph with five
--   pairwise disjoint boundary regions can have min-cut entropies given by `Sw`.
--   Since `Sw` satisfies subadditivity, SSA, weak monotonicity and monogamy, this
--   obstruction is invisible to those four families; it is detected precisely by the
--   cyclic inequality.
--
--   ```lean
--   theorem EmergentGeometry.no_bulk_geometry_realises_Sw(M : HoloModel V) (A₀ A₁ A₂ A₃ A₄ : Region V)
--       (hd : ∀ v, AtMostOneTrue (A₀ v) (A₁ v) (A₂ v) (A₃ v) (A₄ v))
--       (hreal : ∀ b₀ b₁ b₂ b₃ b₄ : Bool,
--         entropy M (unionSel b₀ b₁ b₂ b₃ b₄ A₀ A₁ A₂ A₃ A₄) = (Sw (bmask b₀ b₁ b₂ b₃ b₄) : ℝ)) :
--       False := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/CyclicIndependence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/CyclicIndependence.lean#L150

-- Thm stub generated from Novelty/CyclicIndependence.lean
import Mathlib
import Definitions.Def_Novelty_CyclicIndependence
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Definitions.Def_Novelty_HolographicCyclicInequality

/-!
# Independence of the five-party cyclic inequality, and a non-geometric entropy vector

`Novelty.HolographicCyclicInequality` proves that every min-cut ("holographic")
entropy assignment obeys the five-party cyclic inequality

`∑_j S(A_j A_{j+1}) + S(A₀A₁A₂A₃A₄) ≤ ∑_j S(A_j A_{j+1} A_{j+2})`.

This file establishes that this inequality is *not* a formal consequence of the
standard entropy inequalities available before it, namely

* **subadditivity** `S(XY) ≤ S(X) + S(Y)`,
* **strong subadditivity** `S(XYZ) + S(Y) ≤ S(XY) + S(YZ)`,
* **weak monotonicity** `S(X) + S(Z) ≤ S(XY) + S(YZ)`, and
* **monogamy of mutual information (MMI)**
  `S(XY) + S(YZ) + S(XZ) ≥ S(XYZ) + S(X) + S(Y) + S(Z)`,

by exhibiting an explicit integer-valued five-party entropy vector `Sw` that
satisfies all four families on all pairwise disjoint arguments, yet violates the
cyclic inequality by exactly `1`.

Subsets of the five parties are encoded as bitmasks `0 ≤ m < 32`; unions become
`|||` and disjointness becomes `&&& = 0`.  All four validity families are
verified by kernel evaluation over the full `32³ = 32768` case space of triples
of masks — this is a genuine exhaustive computation, not a definitional
unfolding.

The consequence for emergent geometry: **no** bulk graph whatsoever can produce
this entropy vector (`no_bulk_geometry_realises_Sw`).  So the geometric states
form a strictly smaller cone than the quantum-mechanically consistent ones, and
"reconstruct the geometry from the entanglement" has a genuine obstruction that
is invisible to subadditivity, SSA, weak monotonicity and monogamy alone.
-/

noncomputable section

open EmergentGeometry

open Finset

/-! ## The witness vector -/



/-! ## The four validity families

Each is checked exhaustively over all masks below `32`. -/






/-! ## Packaging the independence statement -/







/-! ## No bulk geometry realises the witness -/

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem EmergentGeometry.no_bulk_geometry_realises_Sw(M : HoloModel V) (A₀ A₁ A₂ A₃ A₄ : Region V)
    (hd : ∀ v, AtMostOneTrue (A₀ v) (A₁ v) (A₂ v) (A₃ v) (A₄ v))
    (hreal : ∀ b₀ b₁ b₂ b₃ b₄ : Bool,
      entropy M (unionSel b₀ b₁ b₂ b₃ b₄ A₀ A₁ A₂ A₃ A₄) = (Sw (bmask b₀ b₁ b₂ b₃ b₄) : ℝ)) :
    False := by sorry
