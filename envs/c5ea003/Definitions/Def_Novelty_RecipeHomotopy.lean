-- Prove2me | Definitions.Def_Novelty_RecipeHomotopy
-- name    : Novelty_RecipeHomotopy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:38:23.970655+00:00
-- url     : https://prove2.me/theorems/24805035-95a1-425d-ae2b-e296d28d294a
-- title:
--   Aether Catalog definitions — Novelty_RecipeHomotopy
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.RecipeHomotopy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/RecipeHomotopy.lean by skeleton subtraction
import Mathlib

/-!
# Recipe substitution spaces

This file gives a finite, combinatorial model of the proposed recipe spaces.  A recipe has
an observable `Core` (its flavor profile) and an unobserved `Optional` component (choices
such as nuts).  The fiber over a fixed flavor is proved equivalent to `Optional`.

For `n` independent binary substitutions, recipes form the vertices of an `n`-cube.
A method is a list of substitutions.  Its endpoint is completely classified by a Boolean
parity vector (`signature`).  This also proves cancellation and commuting-square laws,
the elementary path and 2-cell structure of the cube.
-/

namespace RecipeHomotopy

structure Recipe (Core Optional : Type*) where
  core : Core
  optional : Optional

variable {Core Optional : Type*}

def flavor (r : Recipe Core Optional) : Core := r.core

def FlavorFiber (d : Core) := {r : Recipe Core Optional // flavor r = d}

/-- Recipes with fixed flavor `d` are exactly their optional ingredient data. -/
def fiberEquiv (d : Core) : FlavorFiber (Optional := Optional) d ≃ Optional where
  toFun r := r.1.optional
  invFun o := ⟨⟨d, o⟩, rfl⟩
  left_inv := by
    intro r
    apply Subtype.ext
    cases r with
    | mk r h =>
      cases r with
      | mk c o =>
        simp only [flavor] at h
        cases h
        rfl
  right_inv := by intro o; rfl



abbrev CubeRecipe (n : ℕ) := Fin n → Bool
abbrev Method (n : ℕ) := List (Fin n)

/-- Toggle one binary ingredient choice. -/
def toggle {n : ℕ} (i : Fin n) (r : CubeRecipe n) : CubeRecipe n :=
  fun j => if j = i then !r j else r j

/-- Execute a substitution method from left to right. -/
def follow {n : ℕ} : CubeRecipe n → Method n → CubeRecipe n
  | r, [] => r
  | r, i :: p => follow (toggle i r) p

/-- The parity vector of a method: which choices it toggles an odd number of times. -/
def signature {n : ℕ} : Method n → CubeRecipe n
  | [] => fun _ => false
  | i :: p => toggle i (signature p)











end RecipeHomotopy


