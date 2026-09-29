-- Prove2me | Definitions.Def_EML_GameTheory_RepulsorTheory
-- name    : EML_GameTheory_RepulsorTheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:21:27.880411+00:00
-- url     : https://prove2.me/theorems/f3c4fb4f-b999-48db-a46a-602198a8b362
-- title:
--   Aether Catalog definitions — EML_GameTheory_RepulsorTheory
-- statement:
--   Definition bundle for the Aether Catalog module `EML.GameTheory.RepulsorTheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/GameTheory/RepulsorTheory.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Physics.Classical.RepulsorTheory

Auto-generated from theorem catalog database.
Domain: Physics/Classical
Declarations: 33
-/

noncomputable section


/-- **Diagonal Evasion with Constructive Witness.**
We can explicitly construct the evading function: at position n,
simply differ from enum(n)(n) by adding 1. -/
def diagonal_evader (enum : ℕ → (ℕ → ℕ)) : ℕ → ℕ :=
  fun n => enum n n + 1


/-- **Iterated Diagonal Evasion.**
Even if you add the evader back to the enumeration and re-diagonalize,
you get a *new* evader. The evasion never terminates — this is the
"search-hardening" property at its most fundamental. -/
def iterated_evader : ℕ → (ℕ → (ℕ → ℕ)) → (ℕ → ℕ)
  | 0, enum => diagonal_evader enum
  | n + 1, enum =>
    let prev := iterated_evader n enum
    -- Extend the enumeration with the previous evader
    let extended : ℕ → (ℕ → ℕ) := fun k =>
      if k = 0 then prev else enum (k - 1)
    diagonal_evader extended



/-- **The Evading Set**: explicitly constructed via diagonalization. -/
def evading_set {α : Type*} (f : α → Set α) : Set α :=
  {a : α | a ∉ f a}


/-- A search game on a finite universe of size n.
The target is hidden; the searcher queries positions one at a time.
After k queries that all miss, the evader's remaining hiding places. -/
def remaining_positions (n : ℕ) (queries : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ \ queries
















/-- **The Repulsor Hierarchy.**
Repulsors form a strict hierarchy: a Level-k repulsor evades all searches
of depth k, but not necessarily depth k+1.
Here we model this: a function evades an enumeration at level k if it
differs from the first k functions. -/
def evades_at_level (g : ℕ → ℕ) (enum : ℕ → (ℕ → ℕ)) (k : ℕ) : Prop :=
  ∀ i, i < k → g i ≠ enum i i









end


