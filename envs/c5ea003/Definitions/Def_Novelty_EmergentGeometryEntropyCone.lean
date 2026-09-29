-- Prove2me | Definitions.Def_Novelty_EmergentGeometryEntropyCone
-- name    : Novelty_EmergentGeometryEntropyCone
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:12:15.133819+00:00
-- url     : https://prove2.me/theorems/8ac005e1-1f16-4bce-b118-373c5d254ab0
-- title:
--   Aether Catalog definitions — Novelty_EmergentGeometryEntropyCone
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.EmergentGeometryEntropyCone`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/EmergentGeometryEntropyCone.lean by skeleton subtraction
import Mathlib

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

namespace EmergentGeometry

open Finset

variable {V : Type*} [Fintype V]

/-! ## Boolean separation indicators -/

/-- The separation indicator of two Boolean values: `1` if they differ. -/
def sepBit (a b : Bool) : ℕ := if a = b then 0 else 1




/-- **Submodularity at the level of a single pair of cells.** -/
lemma sepBit_submodular (a₁ a₂ b₁ b₂ : Bool) :
    sepBit (a₁ && a₂) (b₁ && b₂) + sepBit (a₁ || a₂) (b₁ || b₂)
      ≤ sepBit a₁ b₁ + sepBit a₂ b₂ := by
  revert a₁ a₂ b₁ b₂; decide

/-- **The monogamy recombination inequality at the level of a single pair of
cells.**  The three "minority" regions (in exactly two of the three cuts) and
the union region together separate any given pair of bulk cells at most as often
as the three original cuts do.  This is the combinatorial heart of monogamy of
mutual information; it is a genuine 64-case Boolean fact, and it *fails* if the
minority regions are replaced by the naive pairwise intersections. -/
lemma sepBit_mmi (a₁ a₂ a₃ b₁ b₂ b₃ : Bool) :
    sepBit (a₁ && a₂ && !a₃) (b₁ && b₂ && !b₃)
      + sepBit (a₁ && a₃ && !a₂) (b₁ && b₃ && !b₂)
      + sepBit (a₂ && a₃ && !a₁) (b₂ && b₃ && !b₁)
      + sepBit (a₁ || a₂ || a₃) (b₁ || b₂ || b₃)
      ≤ sepBit a₁ b₁ + sepBit a₂ b₂ + sepBit a₃ b₃ := by
  revert a₁ a₂ a₃ b₁ b₂ b₃; decide


/-! ## Bulk geometries and cuts -/

/-- A finite bulk geometry: a symmetric, nonnegatively weighted graph on `V`. -/
structure BulkGraph (V : Type*) [Fintype V] where
  /-- Area element assigned to the pair `(u,v)` of bulk cells. -/
  weight : V → V → ℝ
  weight_symm : ∀ u v, weight u v = weight v u
  weight_nonneg : ∀ u v, 0 ≤ weight u v

/-- A bulk region is a Boolean subset of the bulk cells. -/
abbrev Region (V : Type*) := V → Bool

/-- The area (total cut weight) of the surface bounding a bulk region. -/
def cutWeight (G : BulkGraph V) (f : Region V) : ℝ :=
  (∑ u, ∑ v, (sepBit (f u) (f v) : ℝ) * G.weight u v) / 2







/-! ## Holographic models and min-cut entropy -/

variable [DecidableEq V]

/-- A holographic model: a bulk geometry together with a distinguished set of
boundary cells carrying the quantum degrees of freedom. -/
structure HoloModel (V : Type*) [Fintype V] extends BulkGraph V where
  /-- The boundary cells. -/
  bdry : V → Bool

/-- A bulk region is *admissible* for the boundary region `A` when it is
homologous to `A`, i.e. its trace on the boundary is exactly `A`. -/
def Admissible (M : HoloModel V) (A f : Region V) : Prop :=
  ∀ v, M.bdry v = true → f v = A v

instance (M : HoloModel V) (A f : Region V) : Decidable (Admissible M A f) := by
  unfold Admissible; infer_instance

/-- The finite set of bulk regions homologous to `A`. -/
def admSet (M : HoloModel V) (A : Region V) : Finset (Region V) :=
  univ.filter (fun f => Admissible M A f)

lemma mem_admSet {M : HoloModel V} {A f : Region V} :
    f ∈ admSet M A ↔ Admissible M A f := by
  simp [admSet]

lemma admSet_nonempty (M : HoloModel V) (A : Region V) : (admSet M A).Nonempty :=
  ⟨A, mem_admSet.2 fun _ _ => rfl⟩

/-- **Ryu–Takayanagi entropy.**  The entanglement entropy of a boundary region
is the area of the minimal bulk surface homologous to it. -/
def entropy (M : HoloModel V) (A : Region V) : ℝ :=
  (admSet M A).inf' (admSet_nonempty M A) (cutWeight M.toBulkGraph)








/-! ## The holographic entropy inequalities -/




/-! ## Mutual information -/

/-- Mutual information of two boundary regions. -/
def mutualInfo (M : HoloModel V) (A B : Region V) : ℝ :=
  entropy M A + entropy M B - entropy M (fun v => A v || B v)



/-- Tripartite information, `I₃ = I(A:B) + I(A:C) - I(A:B∪C)`. -/
def tripartiteInfo (M : HoloModel V) (A B C : Region V) : ℝ :=
  mutualInfo M A B + mutualInfo M A C - mutualInfo M A (fun v => B v || C v)


end EmergentGeometry


