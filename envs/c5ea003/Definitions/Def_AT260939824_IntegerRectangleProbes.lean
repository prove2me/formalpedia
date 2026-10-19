-- Prove2me | Definitions.Def_AT260939824_IntegerRectangleProbes
-- name    : AT260939824_IntegerRectangleProbes
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:44:45.217023+00:00
-- url     : https://prove2.me/theorems/80a313b9-8bf8-4173-9359-ab4bb877791d
-- title:
--   Integer probes for rectangular incidence
-- statement:
--   A probe moves each coordinate of a point strictly into one of the adjacent gaps between integer levels, with the direction selected by a Boolean sign. Coordinatewise probes and inward signs for a cell detect its local incidence. For a positive-width rectangular tiling with covering and uniqueness of relative interiors, constancy of all incident minimal faces forces constancy of the whole incident tile set.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/IntegerRectangleProbes.lean, selected declaration lines 16-17, 19-27, 29-39, 41-59, 61-75, 77-78, 80-93, 95-100, 102-107, 109-141, 143-144, 146-155, 157-178; SHA-256 296acfc6365751d8e37aaa3aec887a269012f58dece095622bc774f66bb3ab11. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RectangularCells
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportModel
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

/-!
# Integer probes for rectangular incidence germs

The probes lie strictly between consecutive integer levels. A rectangle
containing a probe contains its base point, and contains the probe in
its full interior. This gives the orthant-germ argument for boundary
strata using only integer coordinates and actual tile cover.
-/

namespace AbelianTargets
noncomputable section

def integerProbe (r : ℝ) (s : Bool) : ℝ :=
  if s then (r+((Int.floor r : ℝ)+1))/2 else (r+((Int.ceil r : ℝ)-1))/2

theorem integerProbe_pos_bounds (r : ℝ) :
    r < integerProbe r true ∧ (Int.floor r : ℝ) < integerProbe r true ∧
      integerProbe r true < (Int.floor r : ℝ)+1 := by
  have hlo := Int.floor_le r
  have hhi := Int.lt_floor_add_one r
  simp only [integerProbe,if_true]
  constructor
  · linarith
  · constructor <;> linarith

theorem integerProbe_neg_bounds (r : ℝ) :
    integerProbe r false < r ∧ (Int.ceil r : ℝ)-1 < integerProbe r false ∧
      integerProbe r false < (Int.ceil r : ℝ) := by
  have hlo := Int.ceil_lt_add_one r
  have hhi := Int.le_ceil r
  change (r+((Int.ceil r : ℝ)-1))/2 < r ∧
    (Int.ceil r : ℝ)-1 < (r+((Int.ceil r : ℝ)-1))/2 ∧
    (r+((Int.ceil r : ℝ)-1))/2 < (Int.ceil r : ℝ)
  constructor
  · linarith
  · constructor <;> linarith

theorem integerProbe_mem_imp {l u : ℤ} {r : ℝ} (s : Bool)
    (hl : (l : ℝ) ≤ integerProbe r s) (hu : integerProbe r s ≤ (u : ℝ)) :
    (l : ℝ) ≤ r ∧ r ≤ (u : ℝ) ∧
      (l : ℝ) < integerProbe r s ∧ integerProbe r s < (u : ℝ) := by
  cases s
  · obtain ⟨hpr,hcp,hpc⟩ := integerProbe_neg_bounds r
    have hlc : l < Int.ceil r := by exact_mod_cast hl.trans_lt hpc
    have hcu : Int.ceil r-1 < u := by exact_mod_cast hcp.trans_le hu
    have hlc' : (l : ℝ) ≤ (Int.ceil r : ℝ)-1 := by exact_mod_cast (show l ≤ Int.ceil r-1 by omega)
    have hcu' : (Int.ceil r : ℝ) ≤ (u : ℝ) := by exact_mod_cast (show Int.ceil r ≤ u by omega)
    exact ⟨(hlc'.trans hcp.le).trans hpr.le,(Int.le_ceil r).trans hcu',
      hlc'.trans_lt hcp,hpc.trans_le hcu'⟩
  · obtain ⟨hrp,hfp,hpf⟩ := integerProbe_pos_bounds r
    have hlf : l < Int.floor r+1 := by exact_mod_cast hl.trans_lt hpf
    have hfu : Int.floor r < u := by exact_mod_cast hfp.trans_le hu
    have hlf' : (l : ℝ) ≤ (Int.floor r : ℝ) := by exact_mod_cast (show l ≤ Int.floor r by omega)
    have hfu' : (Int.floor r : ℝ)+1 ≤ (u : ℝ) := by exact_mod_cast (show Int.floor r+1 ≤ u by omega)
    exact ⟨hlf'.trans (Int.floor_le r),hrp.le.trans hu,
      hlf'.trans_lt hfp,hpf.trans_le hfu'⟩

theorem integerProbe_into {l u : ℤ} {r : ℝ} (s : Bool)
    (hl : (l : ℝ) ≤ r) (hu : r ≤ (u : ℝ))
    (hside : if s then r < (u : ℝ) else (l : ℝ) < r) :
    (l : ℝ) < integerProbe r s ∧ integerProbe r s < (u : ℝ) := by
  cases s
  · change (l : ℝ) < r at hside
    obtain ⟨hpr,hcp,hpc⟩ := integerProbe_neg_bounds r
    have hlc : l < Int.ceil r := by exact_mod_cast hside.trans_le (Int.le_ceil r)
    have hlc' : (l : ℝ) ≤ (Int.ceil r : ℝ)-1 := by exact_mod_cast (show l ≤ Int.ceil r-1 by omega)
    exact ⟨hlc'.trans_lt hcp,hpr.trans_le hu⟩
  · change r < (u : ℝ) at hside
    obtain ⟨hrp,hfp,hpf⟩ := integerProbe_pos_bounds r
    have hfu : Int.floor r < u := by exact_mod_cast (Int.floor_le r).trans_lt hside
    have hfu' : (Int.floor r : ℝ)+1 ≤ (u : ℝ) := by exact_mod_cast (show Int.floor r+1 ≤ u by omega)
    exact ⟨hl.trans_lt hrp,hpf.trans_le hfu'⟩

def rectangularProbe {d : ℕ} (x : RealCoordinates d) (s : Fin d → Bool) : RealCoordinates d :=
  fun i => integerProbe (x i) (s i)

theorem RectangularCell.probe_mem_imp {d : ℕ} (R : RectangularCell d)
    (x : RealCoordinates d) (s : Fin d → Bool)
    (hp : rectangularProbe x s ∈ R.closedBox) :
    x ∈ R.closedBox ∧ rectangularProbe x s ∈ R.relativeInterior := by
  have h := fun i => integerProbe_mem_imp (s i) (hp i).1 (hp i).2
  refine ⟨fun i => ⟨(h i).1,(h i).2.1⟩,?_⟩
  intro i
  have hne : R.lower i ≠ R.upper i := by
    intro he
    have hp' := (h i).2.2
    rw [he] at hp'
    exact (lt_irrefl _ (hp'.1.trans hp'.2)).elim
  simp only [hne,if_false]
  exact (h i).2.2

theorem RectangularCell.faceAt_upper_status {d : ℕ} (R : RectangularCell d)
    (hpos : ∀ i,R.lower i < R.upper i) (x : RealCoordinates d) (i : Fin d) :
    (R.faceAt x).lower i = R.upper i ↔ x i = (R.upper i : ℝ) := by
  by_cases hu : x i = (R.upper i : ℝ)
  · simp [RectangularCell.faceAt,hu]
  · simp [RectangularCell.faceAt,hu,ne_of_lt (hpos i)]

theorem RectangularCell.faceAt_lower_status {d : ℕ} (R : RectangularCell d)
    (hpos : ∀ i,R.lower i < R.upper i) (x : RealCoordinates d) (i : Fin d) :
    (R.faceAt x).upper i = R.lower i ↔ x i = (R.lower i : ℝ) := by
  by_cases hl : x i = (R.lower i : ℝ)
  · simp [RectangularCell.faceAt,hl]
  · simp [RectangularCell.faceAt,hl,ne_of_gt (hpos i)]

theorem RectangularCell.probe_transfer {d : ℕ} (R : RectangularCell d)
    (hpos : ∀ i,R.lower i < R.upper i) (x y : RealCoordinates d) (s : Fin d → Bool)
    (hy : y ∈ R.closedBox) (hface : R.faceAt x = R.faceAt y)
    (hp : rectangularProbe x s ∈ R.relativeInterior) :
    rectangularProbe y s ∈ R.relativeInterior := by
  intro i
  have hp' := hp i
  have hne := ne_of_lt (hpos i)
  simp only [hne,if_false] at hp' ⊢
  apply integerProbe_into (s i) (hy i).1 (hy i).2
  cases hs : s i
  · change (R.lower i : ℝ) < y i
    by_contra hn
    have he : y i = (R.lower i : ℝ) := le_antisymm (le_of_not_gt hn) (hy i).1
    have hxe : x i = (R.lower i : ℝ) := by
      apply (R.faceAt_lower_status hpos x i).mp
      rw [hface]
      exact (R.faceAt_lower_status hpos y i).mpr he
    have hpr := (integerProbe_neg_bounds (x i)).1
    simp only [rectangularProbe,hs] at hp'
    rw [hxe] at hpr hp'
    linarith
  · change y i < (R.upper i : ℝ)
    by_contra hn
    have he : y i = (R.upper i : ℝ) := le_antisymm (hy i).2 (le_of_not_gt hn)
    have hxe : x i = (R.upper i : ℝ) := by
      apply (R.faceAt_upper_status hpos x i).mp
      rw [hface]
      exact (R.faceAt_upper_status hpos y i).mpr he
    have hrp := (integerProbe_pos_bounds (x i)).1
    simp only [rectangularProbe,hs] at hp'
    rw [hxe] at hrp hp'
    linarith

def RectangularCell.inwardSigns {d : ℕ} (R : RectangularCell d) (x : RealCoordinates d) : Fin d → Bool :=
  fun i => decide (x i ≠ (R.upper i : ℝ))

theorem RectangularCell.inward_probe {d : ℕ} (R : RectangularCell d)
    (hpos : ∀ i,R.lower i < R.upper i) (x : RealCoordinates d) (hx : x ∈ R.closedBox) :
    rectangularProbe x (R.inwardSigns x) ∈ R.relativeInterior := by
  intro i
  have hi : (R.lower i : ℝ) < (R.upper i : ℝ) := by exact_mod_cast hpos i
  simp only [ne_of_lt (hpos i),if_false]
  apply integerProbe_into _ (hx i).1 (hx i).2
  by_cases hu : x i = (R.upper i : ℝ)
  · simp [inwardSigns,hu,hi]
  · simpa [inwardSigns,hu] using lt_of_le_of_ne (hx i).2 hu

/-- Constancy of the incident minimal faces forces exact constancy of
the incident tile set. This is the boundary-refinement germ argument. -/
theorem incident_tiles_constant_of_faces {d : ℕ} (T : Set (RectangularCell d))
    (hpos : ∀ R ∈ T,∀ i,R.lower i < R.upper i)
    (hcover : ∀ z : RealCoordinates d,∃ R ∈ T,z ∈ R.closedBox)
    (hunique : ∀ R ∈ T,∀ Q ∈ T,(R.relativeInterior ∩ Q.relativeInterior).Nonempty → R = Q)
    (x y : RealCoordinates d)
    (hfaces : ∀ R ∈ T,x ∈ R.closedBox → y ∈ R.closedBox ∧ R.faceAt x = R.faceAt y) :
    ∀ R ∈ T,y ∈ R.closedBox ↔ x ∈ R.closedBox := by
  intro R hR
  constructor
  · intro hyR
    let s := R.inwardSigns y
    have hpR := R.inward_probe (hpos R hR) y hyR
    obtain ⟨Q,hQ,hpQ⟩ := hcover (rectangularProbe x s)
    obtain ⟨hxQ,hpQ'⟩ := Q.probe_mem_imp x s hpQ
    obtain ⟨hyQ,hfaceQ⟩ := hfaces Q hQ hxQ
    have hpyQ := Q.probe_transfer (hpos Q hQ) x y s hyQ hfaceQ hpQ'
    have he := hunique R hR Q hQ ⟨rectangularProbe y s,hpR,hpyQ⟩
    simpa only [he] using hxQ
  · intro hxR
    exact (hfaces R hR hxR).1

end
end AbelianTargets


