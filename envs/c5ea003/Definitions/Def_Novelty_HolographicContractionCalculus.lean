-- Prove2me | Definitions.Def_Novelty_HolographicContractionCalculus
-- name    : Novelty_HolographicContractionCalculus
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:28:56.782109+00:00
-- url     : https://prove2.me/theorems/a0e17b8d-1ecb-4e2a-bbdb-d04936e749f4
-- title:
--   Aether Catalog definitions — Novelty_HolographicContractionCalculus
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.HolographicContractionCalculus`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/HolographicContractionCalculus.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Definitions.Def_Novelty_HolographicCyclicInequality

/-!
# A calculus of holographic entropy inequalities

Monogamy of mutual information and the five-party cyclic inequality were each
proved by exhibiting a Boolean recombination rule for minimal surfaces.  This
file isolates the mechanism as a single structure and a single theorem, turning
"find a holographic entropy inequality" into "find a contraction map".

A `ContractionMap k m` is a map `χ : Bool^k → Bool^m` that does not increase
Hamming distance.  Given `k` boundary regions `A i` and `m` boundary regions
`B j` whose boundary indicator patterns are related by `χ`, the theorem
`entropy_le_of_contraction` yields

`∑ j S(B j) ≤ ∑ i S(A i)`.

Subadditivity, strong subadditivity and monogamy are all recovered as
instances (`subadditive_of_contraction`, `ssa_of_contraction`,
`mmi_of_contraction`), and `entropy_cyclic5` of
`Novelty.HolographicCyclicInequality` is the instance attached to the cyclic
rule `cyc`.
-/

noncomputable section

namespace EmergentGeometry

open Finset

variable {V : Type*} [Fintype V]

/-- A contraction map: a Boolean map that does not increase Hamming distance.
Each one encodes a holographic entropy inequality. -/
structure ContractionMap (k m : ℕ) where
  /-- The underlying Boolean recombination rule. -/
  toFun : (Fin k → Bool) → (Fin m → Bool)
  /-- Hamming contraction. -/
  contract : ∀ a b : Fin k → Bool,
    ∑ j, sepBit (toFun a j) (toFun b j) ≤ ∑ i, sepBit (a i) (b i)

variable [DecidableEq V]


/-! ## The classical inequalities as contraction maps -/

/-- Intersection-union: the contraction map behind subadditivity and strong
subadditivity. -/
def interUnionMap : ContractionMap 2 2 where
  toFun a := ![a 0 && a 1, a 0 || a 1]
  contract a b := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact sepBit_submodular (a 0) (a 1) (b 0) (b 1)

/-- The minority/union map behind monogamy of mutual information. -/
def minorityMap : ContractionMap 3 4 where
  toFun a := ![a 0 && a 1 && !(a 2), a 0 && a 2 && !(a 1), a 1 && a 2 && !(a 0),
    a 0 || a 1 || a 2]
  contract a b := by
    simp only [Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three]
    exact sepBit_mmi (a 0) (a 1) (a 2) (b 0) (b 1) (b 2)





end EmergentGeometry


