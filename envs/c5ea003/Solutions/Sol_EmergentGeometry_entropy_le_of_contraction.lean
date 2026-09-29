-- Prove2me | solution 1 for EmergentGeometry.entropy_le_of_contraction
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:56:17.878522+00:00
-- url     : https://prove2.me/submissions/00882a23-cb03-41ce-a957-d111a4a1128d

-- Sol generated from Novelty/HolographicContractionCalculus.lean
import Mathlib
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Definitions.Def_Novelty_HolographicContractionCalculus
import Definitions.Def_Novelty_HolographicCyclicInequality
import Theorems.Thm_EmergentGeometry_cutWeight_comb
import Theorems.Thm_EmergentGeometry_entropy_le_of_admissible
import Theorems.Thm_EmergentGeometry_exists_minimal_surface

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


/-! ## The classical inequalities as contraction maps -/








open EmergentGeometry in
theorem solution{k m : ℕ} (M : HoloModel V)
    (A : Fin k → Region V) (B : Fin m → Region V) (χ : ContractionMap k m)
    (hcompat : ∀ v, M.bdry v = true → ∀ j, χ.toFun (fun i => A i v) j = B j v) :
    ∑ j, entropy M (B j) ≤ ∑ i, entropy M (A i) := by
  choose F hF hFval using fun i => exists_minimal_surface M (A i)
  set G : Fin m → Region V := fun j v => χ.toFun (fun i => F i v) j with hG
  have hadm : ∀ j, Admissible M (B j) (G j) := by
    intro j v hv
    show χ.toFun (fun i => F i v) j = B j v
    have : (fun i => F i v) = fun i => A i v := funext fun i => hF i v hv
    rw [this]
    exact hcompat v hv j
  have hcut : ∑ j, cutWeight M.toBulkGraph (G j) ≤ ∑ i, cutWeight M.toBulkGraph (F i) :=
    cutWeight_comb M.toBulkGraph F G (fun u v _ => χ.contract _ _)
  calc ∑ j, entropy M (B j) ≤ ∑ j, cutWeight M.toBulkGraph (G j) :=
        Finset.sum_le_sum fun j _ => entropy_le_of_admissible (hadm j)
    _ ≤ ∑ i, cutWeight M.toBulkGraph (F i) := hcut
    _ = ∑ i, entropy M (A i) := (Finset.sum_congr rfl fun i _ => (hFval i).symm)
