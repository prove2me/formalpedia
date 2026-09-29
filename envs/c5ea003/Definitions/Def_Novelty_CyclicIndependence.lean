-- Prove2me | Definitions.Def_Novelty_CyclicIndependence
-- name    : Novelty_CyclicIndependence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:13:12.64111+00:00
-- url     : https://prove2.me/theorems/924e94eb-fa21-475d-984f-500f6232d9a8
-- title:
--   Aether Catalog definitions — Novelty_CyclicIndependence
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.CyclicIndependence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/CyclicIndependence.lean by skeleton subtraction
import Mathlib
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

namespace EmergentGeometry

open Finset

/-! ## The witness vector -/

/-- An explicit five-party entropy vector, indexed by bitmasks `0 ≤ m < 32`
(bit `i` = party `i`).  Found by local search over integer vectors subject to
subadditivity, strong subadditivity, weak monotonicity and monogamy. -/
def Sw : ℕ → ℕ
  | 0 => 0  | 1 => 3  | 2 => 2  | 3 => 5  | 4 => 4  | 5 => 5  | 6 => 6  | 7 => 5
  | 8 => 2  | 9 => 5  | 10 => 4 | 11 => 7 | 12 => 6 | 13 => 6 | 14 => 7 | 15 => 5
  | 16 => 3 | 17 => 6 | 18 => 5 | 19 => 7 | 20 => 5 | 21 => 4 | 22 => 6 | 23 => 4
  | 24 => 4 | 25 => 5 | 26 => 6 | 27 => 6 | 28 => 4 | 29 => 3 | 30 => 5 | 31 => 2
  | _ => 0


/-! ## The four validity families

Each is checked exhaustively over all masks below `32`. -/






/-! ## Packaging the independence statement -/

/-- Subadditivity as a predicate on entropy vectors indexed by five-party
bitmasks. -/
def SatisfiesSA (S : ℕ → ℕ) : Prop :=
  ∀ X < 32, ∀ Y < 32, X &&& Y = 0 → S (X ||| Y) ≤ S X + S Y

/-- Strong subadditivity as a predicate on entropy vectors. -/
def SatisfiesSSA (S : ℕ → ℕ) : Prop :=
  ∀ X < 32, ∀ Y < 32, ∀ Z < 32, X &&& Y = 0 → Y &&& Z = 0 → X &&& Z = 0 →
    S (X ||| Y ||| Z) + S Y ≤ S (X ||| Y) + S (Y ||| Z)

/-- Weak monotonicity as a predicate on entropy vectors. -/
def SatisfiesWM (S : ℕ → ℕ) : Prop :=
  ∀ X < 32, ∀ Y < 32, ∀ Z < 32, X &&& Y = 0 → Y &&& Z = 0 → X &&& Z = 0 →
    S X + S Z ≤ S (X ||| Y) + S (Y ||| Z)

/-- Monogamy of mutual information as a predicate on entropy vectors. -/
def SatisfiesMMI (S : ℕ → ℕ) : Prop :=
  ∀ X < 32, ∀ Y < 32, ∀ Z < 32, X &&& Y = 0 → Y &&& Z = 0 → X &&& Z = 0 →
    S (X ||| Y ||| Z) + S X + S Y + S Z ≤ S (X ||| Y) + S (Y ||| Z) + S (X ||| Z)

/-- The cyclic inequality for the five singleton parties. -/
def SatisfiesCyclic5 (S : ℕ → ℕ) : Prop :=
  S 3 + S 6 + S 12 + S 24 + S 17 + S 31 ≤ S 7 + S 14 + S 28 + S 25 + S 19


/-! ## No bulk geometry realises the witness -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The union of the sub-family of `A₀ … A₄` selected by five Boolean flags. -/
def unionSel (b₀ b₁ b₂ b₃ b₄ : Bool) (A₀ A₁ A₂ A₃ A₄ : Region V) : Region V :=
  fun v => (b₀ && A₀ v) || (b₁ && A₁ v) || (b₂ && A₂ v) || (b₃ && A₃ v) || (b₄ && A₄ v)

/-- The bitmask named by five Boolean flags. -/
def bmask (b₀ b₁ b₂ b₃ b₄ : Bool) : ℕ :=
  b₀.toNat + 2 * b₁.toNat + 4 * b₂.toNat + 8 * b₃.toNat + 16 * b₄.toNat


end EmergentGeometry


