-- Prove2me | Theorems.Thm_EmergentGeometry_entropy_le_of_contraction
-- name    : EmergentGeometry.entropy_le_of_contraction
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:40:11.659888+00:00
-- url     : https://prove2.me/theorems/7286a71b-48e6-4e9c-9993-f706235b04ec
-- title:
--   The contraction principle.
-- statement:
--   **The contraction principle.**  If the boundary patterns of `m` regions
--   `B j` arise from the boundary patterns of `k` regions `A i` through a
--   contraction map, then the total entropy of the `B`'s is at most the total
--   entropy of the `A`'s.
--
--   ```lean
--   theorem EmergentGeometry.entropy_le_of_contraction{k m : ℕ} (M : HoloModel V)
--       (A : Fin k → Region V) (B : Fin m → Region V) (χ : ContractionMap k m)
--       (hcompat : ∀ v, M.bdry v = true → ∀ j, χ.toFun (fun i => A i v) j = B j v) :
--       ∑ j, entropy M (B j) ≤ ∑ i, entropy M (A i) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/HolographicContractionCalculus.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/HolographicContractionCalculus.lean#L45

-- Thm stub generated from Novelty/HolographicContractionCalculus.lean
import Mathlib
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Definitions.Def_Novelty_HolographicContractionCalculus
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

open EmergentGeometry

open Finset

variable {V : Type*} [Fintype V]


variable [DecidableEq V]

theorem EmergentGeometry.entropy_le_of_contraction{k m : ℕ} (M : HoloModel V)
    (A : Fin k → Region V) (B : Fin m → Region V) (χ : ContractionMap k m)
    (hcompat : ∀ v, M.bdry v = true → ∀ j, χ.toFun (fun i => A i v) j = B j v) :
    ∑ j, entropy M (B j) ≤ ∑ i, entropy M (A i) := by sorry
