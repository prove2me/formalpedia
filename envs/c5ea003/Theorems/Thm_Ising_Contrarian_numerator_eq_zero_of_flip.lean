-- Prove2me | Theorems.Thm_Ising_Contrarian_numerator_eq_zero_of_flip
-- name    : Ising.Contrarian.numerator_eq_zero_of_flip
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:53:07.693771+00:00
-- url     : https://prove2.me/theorems/0eaf810e-2bea-46db-91d2-1cd73ffffc8e
-- title:
--   Reindexing by an involutive symmetry and using oddness makes the
-- statement:
--   Reindexing by an involutive symmetry and using oddness makes the
--   unnormalised magnetization vanish exactly.
--
--   ```lean
--   theorem Ising.Contrarian.numerator_eq_zero_of_flip    (flip : Ω → Ω) (energy observable : Ω → ℝ) (β : ℝ)
--       (hflip : Function.Involutive flip)
--       (henergy : ∀ ω, energy (flip ω) = energy ω)
--       (hodd : ∀ ω, observable (flip ω) = -observable ω) :
--       numerator β energy observable = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/IsingModel/Contrarian.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/IsingModel/Contrarian.lean#L44

-- Thm stub generated from Applications/IsingModel/Contrarian.lean
import Mathlib
import Definitions.Def_Applications_IsingModel_Contrarian

/-!
# Contrarian results for finite-volume Ising symmetry

A frequently stated but false finite-volume version of spontaneous symmetry
breaking says that a zero-field Gibbs state can already have nonzero expected
magnetization.  The theorem below proves the opposite in a model-independent
finite setting: any finite Gibbs ensemble with a fixed-point-free or non-fixed-
point-free involutive spin flip, flip-invariant energy, and odd magnetization has
exactly zero expected magnetization.

This does not contradict the infinite-volume Ising transition.  Spontaneous
magnetization requires first selecting plus boundary conditions (or a positive
field) and then taking a thermodynamic limit; the symmetric finite-volume state
is always the equal mixture of its two flipped phases.
-/

noncomputable section

open Ising.Contrarian

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem Ising.Contrarian.numerator_eq_zero_of_flip    (flip : Ω → Ω) (energy observable : Ω → ℝ) (β : ℝ)
    (hflip : Function.Involutive flip)
    (henergy : ∀ ω, energy (flip ω) = energy ω)
    (hodd : ∀ ω, observable (flip ω) = -observable ω) :
    numerator β energy observable = 0 := by sorry
