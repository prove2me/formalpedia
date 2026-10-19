-- Prove2me | Definitions.Def_AT260939824_AnisotropicMarkers
-- name    : AT260939824_AnisotropicMarkers
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:44:09.139396+00:00
-- url     : https://prove2.me/theorems/0a81fb1a-e112-4a77-afbe-d83ca7d69334
-- title:
--   Anisotropic clopen marker data
-- statement:
--   For a lattice action on $X$ and integer scales $L_i$, the displacement graph joins points related by a nonzero $g\in\mathbb Z^d$ satisfying $|g_i|\le L_i$ in every coordinate. An anisotropic marker set $M$ is clopen, separates distinct orbit markers by more than $L_i$ in some coordinate, and meets every coordinate box of those radii.
--
--   This packages the separation and covering requirements used in rectangular orbit decompositions.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 3; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/AnisotropicMarkers.lean, selected declaration lines 15-16, 18-21, 23-27, 31-40, 99-105; SHA-256 3009ed642985035e32ca3a8b04afdbc1f45897ae80d2d903e683f0a3c5abc407. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Profinite

set_option autoImplicit false

/-!
# Clopen markers at independent coordinate scales

The initial marker construction in Lemma 3.2 is proved for an actual free
continuous action. Each coordinate has its own scale. This is the input
to the later packing, priority, cut, and rectangular subdivision steps.
-/

namespace AbelianTargets

noncomputable section

def anisotropicDisplacements {d : ℕ} (L : Fin d → ℕ) : Finset (Lattice d) :=
  (Fintype.piFinset (fun i => Finset.Icc (-(L i : ℤ)) (L i : ℤ))).filter (· ≠ 0)

theorem mem_anisotropicDisplacements {d : ℕ} (L : Fin d → ℕ) (g : Lattice d) :
    g ∈ anisotropicDisplacements L ↔ (∀ i, |g i| ≤ (L i : ℤ)) ∧ g ≠ 0 := by
  simp only [anisotropicDisplacements, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_Icc, abs_le]

theorem neg_mem_anisotropicDisplacements {d : ℕ} {L : Fin d → ℕ} {g : Lattice d}
    (hg : g ∈ anisotropicDisplacements L) : -g ∈ anisotropicDisplacements L := by
  obtain ⟨hbound,hne⟩ := (mem_anisotropicDisplacements L g).mp hg
  exact (mem_anisotropicDisplacements L (-g)).mpr
    ⟨by simpa only [Pi.neg_apply,abs_neg] using hbound,neg_ne_zero.mpr hne⟩

variable {d : ℕ} {X : Type*} [TopologicalSpace X] [AddAction (Lattice d) X]

def anisotropicDisplacementGraph (L : Fin d → ℕ)
    (free : IsFree (G := Lattice d) (X := X)) : SimpleGraph X where
  Adj x y := ∃ g ∈ anisotropicDisplacements L, g +ᵥ x = y
  symm := by
    rintro x y ⟨g,hg,hxy⟩
    refine ⟨-g,neg_mem_anisotropicDisplacements hg,?_⟩
    rw [← hxy,← add_vadd,neg_add_cancel,zero_vadd]
  loopless := ⟨by
    rintro x ⟨g,hg,hfix⟩
    exact ((mem_anisotropicDisplacements L g).mp hg).2 (free g x hfix)⟩

variable [ContinuousVAdd (Lattice d) X]



variable [T1Space X] [SecondCountableTopology X]



structure AnisotropicClopenMarkers (d : ℕ) (L : Fin d → ℕ) (X : Type*)
    [TopologicalSpace X] [AddAction (Lattice d) X] where
  markers : Set X
  clopen : IsClopen markers
  separated : ∀ (x : X) (u v : Lattice d),u +ᵥ x ∈ markers → v +ᵥ x ∈ markers → u ≠ v →
    ∃ i,(L i : ℤ) < |u i-v i|
  covering : ∀ (x : X) (u : Lattice d),∃ v : Lattice d,v +ᵥ x ∈ markers ∧ ∀ i,|u i-v i| ≤ (L i : ℤ)



end

end AbelianTargets


