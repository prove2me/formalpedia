-- Prove2me | Definitions.Def_Logic_PosetTheory_PhantomTopologies
-- name    : Logic_PosetTheory_PhantomTopologies
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:00:13.26444+00:00
-- url     : https://prove2.me/theorems/598bbdbf-fa29-4c28-aca5-5401e7a6b1de
-- title:
--   Aether Catalog definitions — Logic_PosetTheory_PhantomTopologies
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.PosetTheory.PhantomTopologies`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/PosetTheory/PhantomTopologies.lean by skeleton subtraction
import Mathlib
/-
# Phantom Topologies

A phantom topology is an observer-indexed family of topologies.  This file makes
"agreement" precise as the supremum in Mathlib's (reverse-inclusion) lattice of
topologies and develops a chain of results from the general definition to two
substantive examples.

The literal proposed phantom number is degenerate: every topology has a
one-observer representation, obtained by letting that observer see the real
topology itself.  A nontrivial variant requires every observer to be strictly
finer than consensus.  For that variant, the standard topology on `ℝ` has a
genuine two-observer representation by the lower- and upper-limit topologies.
The proposed lower bound for nonmetrizable spaces is false: the indiscrete
space on `Bool` is nonmetrizable yet is the consensus of two strictly finer
Sierpiński topologies.
-/

open Set TopologicalSpace

namespace PhantomTopology

variable {X ι : Type*}

/-- An observer-indexed family of topologies. -/
abbrev System (ι X : Type*) := ι → TopologicalSpace X

/-- The topology consisting of the opens on which every observer agrees. -/
def consensus (T : System ι X) : TopologicalSpace X := ⨆ i, T i



/-- The literal definition always admits a one-observer representation. -/
def singletonSystem (τ : TopologicalSpace X) : System Unit X := fun _ => τ



/-- A representation is genuinely phantom when every observer sees strictly
more opens than the consensus. -/
def Genuine (T : System ι X) : Prop := ∀ i, T i < consensus T


/-! ## The real line: two half-open observers -/

/-- Lower-limit openness: each point starts a contained interval `[x,b)`. -/
def lowerOpen (U : Set ℝ) : Prop := ∀ x ∈ U, ∃ b, x < b ∧ Ico x b ⊆ U

/-- Upper-limit openness: each point ends a contained interval `(a,x]`. -/
def upperOpen (U : Set ℝ) : Prop := ∀ x ∈ U, ∃ a, a < x ∧ Ioc a x ⊆ U

/-- The lower-limit (Sorgenfrey) topology on `ℝ`. -/
def lowerTop : TopologicalSpace ℝ where
  IsOpen := lowerOpen
  isOpen_univ := fun x _ => ⟨x + 1, by linarith, by simp⟩
  isOpen_inter s t hs ht := by
    intro x hx
    obtain ⟨b₁, hb₁, hs₁⟩ := hs x hx.1
    obtain ⟨b₂, hb₂, ht₂⟩ := ht x hx.2
    refine ⟨min b₁ b₂, lt_min hb₁ hb₂, ?_⟩
    intro y hy
    exact ⟨hs₁ ⟨hy.1, lt_of_lt_of_le hy.2 (min_le_left _ _)⟩,
      ht₂ ⟨hy.1, lt_of_lt_of_le hy.2 (min_le_right _ _)⟩⟩
  isOpen_sUnion S hS := by
    intro x hx
    obtain ⟨U, hUS, hxU⟩ := hx
    obtain ⟨b, hb, hsub⟩ := hS U hUS x hxU
    exact ⟨b, hb, fun y hy => ⟨U, hUS, hsub hy⟩⟩

/-- The upper-limit topology on `ℝ`. -/
def upperTop : TopologicalSpace ℝ where
  IsOpen := upperOpen
  isOpen_univ := fun x _ => ⟨x - 1, by linarith, by simp⟩
  isOpen_inter s t hs ht := by
    intro x hx
    obtain ⟨a₁, ha₁, hs₁⟩ := hs x hx.1
    obtain ⟨a₂, ha₂, ht₂⟩ := ht x hx.2
    refine ⟨max a₁ a₂, max_lt ha₁ ha₂, ?_⟩
    intro y hy
    exact ⟨hs₁ ⟨lt_of_le_of_lt (le_max_left _ _) hy.1, hy.2⟩,
      ht₂ ⟨lt_of_le_of_lt (le_max_right _ _) hy.1, hy.2⟩⟩
  isOpen_sUnion S hS := by
    intro x hx
    obtain ⟨U, hUS, hxU⟩ := hx
    obtain ⟨a, ha, hsub⟩ := hS U hUS x hxU
    exact ⟨a, ha, fun y hy => ⟨U, hUS, hsub hy⟩⟩


/-- The two real-line observers, indexed by `Bool`. -/
def realObservers : System Bool ℝ := fun b => if b then lowerTop else upperTop









/-! ## A nonmetrizable two-observer counterexample -/

/-- The Sierpiński topology whose extra open singleton is `{true}`. -/
def sierpTrue : TopologicalSpace Bool where
  IsOpen U := false ∈ U → true ∈ U
  isOpen_univ := by intro _; trivial
  isOpen_inter s t hs ht := by intro h; exact ⟨hs h.1, ht h.2⟩
  isOpen_sUnion S hS := by
    rintro ⟨U, hUS, hfU⟩
    exact ⟨U, hUS, hS U hUS hfU⟩

/-- The opposite Sierpiński topology, with extra open singleton `{false}`. -/
def sierpFalse : TopologicalSpace Bool where
  IsOpen U := true ∈ U → false ∈ U
  isOpen_univ := by intro _; trivial
  isOpen_inter s t hs ht := by intro h; exact ⟨hs h.1, ht h.2⟩
  isOpen_sUnion S hS := by
    rintro ⟨U, hUS, htU⟩
    exact ⟨U, hUS, hS U hUS htU⟩



/-- The two Sierpiński observers. -/
def boolObservers : System Bool Bool := fun b => if b then sierpTrue else sierpFalse




end PhantomTopology


