-- Prove2me | solution 1 for Ising.Contrarian.numerator_eq_zero_of_flip
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:21:48.032569+00:00
-- url     : https://prove2.me/submissions/813869d0-1d24-4730-8dcd-66e75d62c089

-- Sol generated from Applications/IsingModel/Contrarian.lean
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










open Ising.Contrarian in
theorem solution    (flip : Ω → Ω) (energy observable : Ω → ℝ) (β : ℝ)
    (hflip : Function.Involutive flip)
    (henergy : ∀ ω, energy (flip ω) = energy ω)
    (hodd : ∀ ω, observable (flip ω) = -observable ω) :
    numerator β energy observable = 0 := by
  unfold numerator
  -- Reindex the sum by flip
  have h : ∑ ω, Real.exp (-β * energy ω) * observable ω = ∑ ω, Real.exp (-β * energy (flip ω)) * observable (flip ω) := by
    rw [← Equiv.sum_comp (Equiv.ofBijective flip (hflip.bijective))]
    simp
  -- Use the symmetry properties to rewrite the reindexed sum as the negative
  have h' : ∑ ω, Real.exp (-β * energy (flip ω)) * observable (flip ω) = ∑ ω, -Real.exp (-β * energy ω) * observable ω := by
    simp [henergy, hodd]
  have h'' : ∑ ω, -Real.exp (-β * energy ω) * observable ω = -∑ ω, Real.exp (-β * energy ω) * observable ω := by
    simp [neg_mul]
  linarith [h, h', h'']
