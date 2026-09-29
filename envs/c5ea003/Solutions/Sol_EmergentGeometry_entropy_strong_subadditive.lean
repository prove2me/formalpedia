-- Prove2me | solution 1 for EmergentGeometry.entropy_strong_subadditive
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:56:20.448301+00:00
-- url     : https://prove2.me/submissions/d0d75446-5706-4fd3-8a78-96af0e518ecb

-- Sol generated from Novelty/EmergentGeometryEntropyCone.lean
import Mathlib
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Theorems.Thm_EmergentGeometry_cutWeight_submodular
import Theorems.Thm_EmergentGeometry_entropy_le_of_admissible
import Theorems.Thm_EmergentGeometry_exists_minimal_surface

/-!
# Emergent geometry from entanglement: the min-cut entropy cone

This file develops, from scratch, the mathematics behind the slogan
*"spacetime geometry is built out of entanglement"* in a finite, fully rigorous
setting.

A **bulk geometry** is a finite weighted graph (symmetric, nonnegative weights):
this is the discrete stand-in for a spatial slice of an asymptotically AdS
geometry, the weight of an edge playing the role of the area of the surface
element separating two bulk cells.  Some vertices are declared **boundary**
vertices; these carry the CFT degrees of freedom.

The **entanglement entropy** of a boundary region `A` is the *min-cut*
(Ryu–Takayanagi) prescription: the minimum cut weight over all bulk regions
whose boundary trace is exactly `A`.

The main results proved here are the *holographic entropy inequalities* of this
model, obtained from purely combinatorial (Boolean) pointwise inequalities on
separation indicators:

* `entropy_subadditive`         : `S(A ∪ B) ≤ S(A) + S(B)`
* `entropy_strong_subadditive`  : `S(A∪B) + S(B∪C) ≥ S(A∪B∪C) + S(B)`
* `entropy_monogamy` (**MMI**)  : `S(A∪B)+S(B∪C)+S(A∪C) ≥ S(A)+S(B)+S(C)+S(A∪B∪C)`
* `entropy_complement`          : purity, `S(A) = S(bdry \ A)`

The key technical engine is `cutWeight_comb`: a family of cuts dominates another
family as soon as the corresponding Boolean separation indicators do so
pointwise.  Strong subadditivity comes from submodularity of the cut function
(`sepBit_submodular`), and monogamy from a *minority/union* recombination of
three cuts, whose 64-case Boolean verification is `sepBit_mmi`.
-/

noncomputable section

open EmergentGeometry

open Finset

variable {V : Type*} [Fintype V]

/-! ## Boolean separation indicators -/








/-! ## Bulk geometries and cuts -/










/-! ## Holographic models and min-cut entropy -/

variable [DecidableEq V]















/-! ## The holographic entropy inequalities -/




/-! ## Mutual information -/







open EmergentGeometry in
theorem solution(M : HoloModel V) (A B C : Region V)
    (hAC : ∀ v, A v = true → C v = false) :
    entropy M (fun v => A v || B v || C v) + entropy M B
      ≤ entropy M (fun v => A v || B v) + entropy M (fun v => B v || C v) := by
  obtain ⟨f, hf, hfval⟩ := exists_minimal_surface M (fun v => A v || B v)
  obtain ⟨g, hg, hgval⟩ := exists_minimal_surface M (fun v => B v || C v)
  have hunion : Admissible M (fun v => A v || B v || C v) (fun v => f v || g v) := by
    intro v hv
    show (f v || g v) = (A v || B v || C v)
    rw [hf v hv, hg v hv]
    cases hA : A v <;> cases hB : B v <;> cases hC : C v <;> simp_all
  have hinter : Admissible M B (fun v => f v && g v) := by
    intro v hv
    show (f v && g v) = B v
    rw [hf v hv, hg v hv]
    cases hA : A v <;> cases hB : B v <;> cases hC : C v <;> simp_all
  have h1 := entropy_le_of_admissible hunion
  have h2 := entropy_le_of_admissible hinter
  have hsub := cutWeight_submodular M.toBulkGraph f g
  rw [hfval, hgval]
  linarith
