-- Prove2me | Definitions.Def_Applications_ClawFreeCubicZeroForcing
-- name    : Applications_ClawFreeCubicZeroForcing
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:39:26.845319+00:00
-- url     : https://prove2.me/theorems/c1d73564-25f6-4dca-b084-16597aca7a2c
-- title:
--   Aether Catalog definitions — Applications_ClawFreeCubicZeroForcing
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.ClawFreeCubicZeroForcing`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/ClawFreeCubicZeroForcing.lean by skeleton subtraction
import Mathlib

/-!
# Claw-free cubic graphs and zero forcing

A finite-set formalization of the color-change rule, together with structural
and extremal results used in the study of claw-free cubic graphs.
-/

open Relation

namespace ClawFreeCubicZeroForcing

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One legal zero-forcing move: a colored vertex `u` has exactly one
uncolored neighbor `w`, which is then added to the colored set. -/
def ForceStep (G : SimpleGraph V) (S T : Finset V) : Prop :=
  ∃ u ∈ S, ∃ w ∉ S, G.Adj u w ∧
    (∀ z, G.Adj u z → z ∉ S → z = w) ∧ T = insert w S

/-- A set is zero forcing when finitely many legal color changes color every vertex. -/
def IsZeroForcing (G : SimpleGraph V) (S : Finset V) : Prop :=
  ReflTransGen (ForceStep G) S Finset.univ

/-- The zero forcing number, defined as the least size of a zero forcing set. -/
noncomputable def zeroForcingNumber (G : SimpleGraph V) : ℕ := by
  classical
  exact Finset.min' (Finset.image Finset.card (Finset.univ.filter (IsZeroForcing G)))
    (by
      refine ⟨Fintype.card V, ?_⟩
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Finset.univ, ReflTransGen.refl, Finset.card_univ⟩)















/-- `ClawFree G` says that no vertex has three distinct, pairwise nonadjacent neighbors. -/
def ClawFree (G : SimpleGraph V) : Prop :=
  ∀ ⦃v a b c : V⦄,
    G.Adj v a → G.Adj v b → G.Adj v c →
    a ≠ b → a ≠ c → b ≠ c →
    G.Adj a b ∨ G.Adj a c ∨ G.Adj b c

/-- Cubicity expressed by cardinality of each finite neighbor set. -/
def Cubic (G : SimpleGraph V) : Prop :=
  ∀ v, (G.neighborSet v).ncard = 3



end ClawFreeCubicZeroForcing


