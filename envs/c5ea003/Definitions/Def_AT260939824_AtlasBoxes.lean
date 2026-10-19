-- Prove2me | Definitions.Def_AT260939824_AtlasBoxes
-- name    : AT260939824_AtlasBoxes
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:44:57.88124+00:00
-- url     : https://prove2.me/theorems/ef6ba7ee-e622-4fb6-9d64-3f20d6e8de71
-- title:
--   Integer cut boxes around anisotropic markers
-- statement:
--   Let $A\subseteq\mathbb Z^d$ be marker centers and let $L_i$ be coordinate scales. Each center $a$ has lower cuts between $a_i-3L_i$ and $a_i-2L_i$, and upper cuts between $a_i+2L_i$ and $a_i+3L_i$. Its real box is
--
--   $$ B_a=\prod_i[\ell_i(a),u_i(a)]. $$
--
--   Positive scales and marker covering give box covering; intersecting boxes have centers separated by at most $6L_i$ in coordinate $i$. These are the initial rectangular domains.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 3; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/AtlasBoxes.lean, selected declaration lines 20-24, 26-28, 38-57, 59-73, 75-82; SHA-256 fd66bcb835dc57709344f27d5a1f02145b5c360849955b9cd6748982b5c14090. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

/-!
# Covering and overlap bounds for the actual marker boxes

Integer cuts in the prescribed ranges give a covering of the ambient
real orbit coordinates. Their sides lie between four and six times
the scale, and intersecting boxes have centers within six scales.
The subsequent retained-box subdivision and regular CW construction
are not supplied by these covering estimates.
-/

namespace AbelianTargets

noncomputable section

structure RectangularCuts {d : ℕ} (L : Fin d → ℕ) (A : Set (Lattice d)) where
  lower : A → Lattice d
  upper : A → Lattice d
  lower_bound : ∀ a i,a.val i-3*(L i : ℤ) ≤ lower a i ∧ lower a i ≤ a.val i-2*(L i : ℤ)
  upper_bound : ∀ a i,a.val i+2*(L i : ℤ) ≤ upper a i ∧ upper a i ≤ a.val i+3*(L i : ℤ)

def RectangularCuts.box {d : ℕ} {L : Fin d → ℕ} {A : Set (Lattice d)}
    (cuts : RectangularCuts L A) (a : A) : Set (RealCoordinates d) :=
  {z | ∀ i,(cuts.lower a i : ℝ) ≤ z i ∧ z i ≤ (cuts.upper a i : ℝ)}



theorem RectangularCuts.cover {d : ℕ} {L : Fin d → ℕ} {A : Set (Lattice d)}
    (cuts : RectangularCuts L A) (hL : ∀ i,1 ≤ L i)
    (hcover : ∀ u : Lattice d,∃ a ∈ A,∀ i,|u i-a i| ≤ (L i : ℤ)) :
    ∀ z : RealCoordinates d,∃ a : A,z ∈ cuts.box a := by
  intro z
  let u : Lattice d := fun i => Int.floor (z i)
  obtain ⟨a,ha,hclose⟩ := hcover u
  refine ⟨⟨a,ha⟩,?_⟩
  intro i
  have hu₀ : (u i : ℝ) ≤ z i := Int.floor_le (z i)
  have hu₁ : z i < (u i : ℝ)+1 := Int.lt_floor_add_one (z i)
  have hclose' : -(L i : ℤ) ≤ u i-a i ∧ u i-a i ≤ (L i : ℤ) := abs_le.mp (hclose i)
  have hl : cuts.lower ⟨a,ha⟩ i ≤ a i-2*(L i : ℤ) := (cuts.lower_bound ⟨a,ha⟩ i).2
  have hh : a i+2*(L i : ℤ) ≤ cuts.upper ⟨a,ha⟩ i := (cuts.upper_bound ⟨a,ha⟩ i).1
  have hLi : (1 : ℤ) ≤ L i := by exact_mod_cast hL i
  have hlow : cuts.lower ⟨a,ha⟩ i ≤ u i := by omega
  have hhigh : u i+1 ≤ cuts.upper ⟨a,ha⟩ i := by omega
  have hlow' : (cuts.lower ⟨a,ha⟩ i : ℝ) ≤ (u i : ℝ) := by exact_mod_cast hlow
  have hhigh' : (u i : ℝ)+1 ≤ (cuts.upper ⟨a,ha⟩ i : ℝ) := by exact_mod_cast hhigh
  exact ⟨hlow'.trans hu₀,hu₁.le.trans hhigh'⟩

theorem RectangularCuts.overlap_centers {d : ℕ} {L : Fin d → ℕ} {A : Set (Lattice d)}
    (cuts : RectangularCuts L A) {a b : A} (hoverlap : (cuts.box a ∩ cuts.box b).Nonempty) :
    ∀ i,|a.val i-b.val i| ≤ 6*(L i : ℤ) := by
  obtain ⟨z,hza,hzb⟩ := hoverlap
  intro i
  have hab' : (cuts.lower a i : ℝ) ≤ (cuts.upper b i : ℝ) := (hza i).1.trans (hzb i).2
  have hba' : (cuts.lower b i : ℝ) ≤ (cuts.upper a i : ℝ) := (hzb i).1.trans (hza i).2
  have hab : cuts.lower a i ≤ cuts.upper b i := by exact_mod_cast hab'
  have hba : cuts.lower b i ≤ cuts.upper a i := by exact_mod_cast hba'
  obtain ⟨hla,_⟩ := cuts.lower_bound a i
  obtain ⟨hlb,_⟩ := cuts.lower_bound b i
  obtain ⟨_,hua⟩ := cuts.upper_bound a i
  obtain ⟨_,hub⟩ := cuts.upper_bound b i
  rw [abs_le]
  omega

/-- The box-cover conclusion specialized to the orbit markers constructed
on an actual action. -/
theorem anisotropic_marker_boxes_cover {d : ℕ} {L : Fin d → ℕ} {X : Type*}
    [TopologicalSpace X] [AddAction (Lattice d) X]
    (M : AnisotropicClopenMarkers d L X) (hL : ∀ i,1 ≤ L i) (x : X)
    (cuts : RectangularCuts L {a : Lattice d | a +ᵥ x ∈ M.markers}) :
    ∀ z : RealCoordinates d,∃ a,z ∈ cuts.box a :=
  cuts.cover hL (M.covering x)

end

end AbelianTargets


