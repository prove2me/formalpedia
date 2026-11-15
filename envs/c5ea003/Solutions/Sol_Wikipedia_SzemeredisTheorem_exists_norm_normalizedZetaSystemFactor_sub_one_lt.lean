-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.exists_norm_normalizedZetaSystemFactor_sub_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:35:06.017692+00:00
-- url     : https://prove2.me/submissions/4644de76-1434-430d-a7ee-b9c5835f46cf

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Theorems.Thm_Wikipedia_SzemeredisTheorem_tendsto_normalizedZetaSystemFactor_zero

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Uniform zeta control near the pole at one

Mathlib completes the singular function

`z ↦ z * riemannZeta (1 + z)`

across `z = 0` by means of the entire function `riemannZeta₁`.  This file
packages that completion in the coordinates used by the
Goldston--Yıldırım argument.  In particular, the completed residue factor
is uniformly close to one on a small complex ball, and the corresponding
two-variable normalized zeta ratio is uniformly close to one on a small
polydisc.

The latter is the stable way to state the zeta comparison: all apparent
singularities have already been removed.  Separate lemmas recover the raw
zeta expressions away from zero.
-/

/-
The completion definitions and their differentiability proofs below are
backported from Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean at
 db584cd6d46c92f209a44c0f1c829460d327499d.
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Terence Tao
-/
section GreenTaoZetaCompatibility

open Set Filter Complex
open scoped Topology





@[simp]
lemma riemannZeta₀_one : riemannZeta₀ 1 = (Real.eulerMascheroniConstant : ℂ) := by simp [riemannZeta₀]

@[simp]
lemma riemannZeta₁_one : riemannZeta₁ 1 = 1 := by simp [riemannZeta₁]









end GreenTaoZetaCompatibility

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators Topology



@[simp]
theorem zetaResidueFactor_zero :
    zetaResidueFactor 0 = 1 := by
  simp [zetaResidueFactor]

















@[simp]
theorem normalizedZetaPairFactor_zero_zero :
    normalizedZetaPairFactor 0 0 = 1 := by
  simp [normalizedZetaPairFactor]









/-! ## Finite systems of paired zeta factors -/



@[simp]
theorem normalizedZetaSystemFactor_zero_zero
    {κ : Type*} [Fintype κ] :
    normalizedZetaSystemFactor
      (0 : κ → ℂ) (0 : κ → ℂ) = 1 := by
  simp [normalizedZetaSystemFactor]



theorem continuousAt_normalizedZetaSystemFactor_zero
    {κ : Type*} [Fintype κ] :
    ContinuousAt
      (fun z : (κ → ℂ) × (κ → ℂ) =>
        normalizedZetaSystemFactor z.1 z.2)
      (0, 0) := by
  simpa only [ContinuousAt,
    normalizedZetaSystemFactor_zero_zero] using
    (tendsto_normalizedZetaSystemFactor_zero
      (κ := κ))





end Wikipedia.SzemeredisTheorem

end
/-!
# Uniform zeta control near the pole at one

Mathlib completes the singular function

`z ↦ z * riemannZeta (1 + z)`

across `z = 0` by means of the entire function `riemannZeta₁`.  This file
packages that completion in the coordinates used by the
Goldston--Yıldırım argument.  In particular, the completed residue factor
is uniformly close to one on a small complex ball, and the corresponding
two-variable normalized zeta ratio is uniformly close to one on a small
polydisc.

The latter is the stable way to state the zeta comparison: all apparent
singularities have already been removed.  Separate lemmas recover the raw
zeta expressions away from zero.
-/
open Wikipedia.SzemeredisTheorem
open Filter
open scoped BigOperators Topology
/-! ## Finite systems of paired zeta factors -/

open Wikipedia.SzemeredisTheorem in
/-- Epsilon--delta form of the finite-system zeta comparison.  The sup norms
give simultaneous control of every Fourier parameter. -/
theorem solution
    {κ : Type*} [Fintype κ]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : κ → ℂ,
        ‖u‖ < δ →
        ‖v‖ < δ →
        ‖normalizedZetaSystemFactor u v - 1‖ < ε := by
  obtain ⟨δ, hδ, hclose⟩ :=
    Metric.continuousAt_iff.mp
      (continuousAt_normalizedZetaSystemFactor_zero
        (κ := κ)) ε hε
  refine ⟨δ, hδ, fun u v hu hv => ?_⟩
  have hdist :
      dist (u, v) (0, 0) < δ := by
    rw [Prod.dist_eq, max_lt_iff]
    constructor <;>
      simpa [dist_eq_norm] using ‹_›
  have := hclose hdist
  simpa [dist_eq_norm] using this
