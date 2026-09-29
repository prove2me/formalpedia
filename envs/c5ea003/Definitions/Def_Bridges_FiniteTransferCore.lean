-- Prove2me | Definitions.Def_Bridges_FiniteTransferCore
-- name    : Bridges_FiniteTransferCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:20:33.041707+00:00
-- url     : https://prove2.me/theorems/82f6675b-34fb-463b-8dad-0e57b700de57
-- title:
--   Aether Catalog definitions — Bridges_FiniteTransferCore
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.FiniteTransferCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/FiniteTransferCore.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite Transfer Dynamics: Eventual Image Stabilization and Recurrent Core

This file establishes the foundational theory of finite transfer dynamics:
given any endomorphism `f` on a finite type, the descending chain of iterated
images stabilizes, yielding a canonical **recurrent core** on which `f`
restricts to a bijection.

## Main Results

* `iterate_range_subset` — `Set.range (f^[n+1]) ⊆ Set.range (f^[n])`.
* `iterate_range_stabilizes` — (Theorem A) For finite `C`, there exists `N`
  such that `Set.range (f^[N+1]) = Set.range (f^[N])`.
* `surjOn_stable_range` — On the stabilized range, `f` is surjective.
* `mapsTo_stable_range` — On the stabilized range, `f` maps into itself.
* `bijOn_stable_range` — (Theorem A corollary) On the stabilized range,
  `f` is bijective — a finite surjective endomorphism is bijective.
* `renorm_comp` — The renormalization semigroup law `f^[m+n] = f^[m] ∘ f^[n]`.

## Mathematical Overview

For any function `f : C → C` on a finite type, the images
`Im(f⁰) ⊇ Im(f¹) ⊇ Im(f²) ⊇ ⋯` form a descending chain of finite sets.
By finiteness this chain stabilizes at some index `N`. On the stable image
`Core := Im(f^N)`, the map `f` is surjective. Since a surjective
endomorphism of a finite set is bijective, `f` restricts to a permutation on
`Core`. The orbits of this permutation are the **recurrent classes** of the
dynamical system.

This is the combinatorial backbone underlying recurrent-class decomposition
in finite Markov chains, terminal SCC analysis in automata theory, and the
spectral boundary construction in closure-scale dynamics.
-/

set_option maxHeartbeats 800000

open Function Set Finset

namespace FiniteTransferDynamics

variable {C : Type*} [Fintype C] [DecidableEq C]

/-! ### Range monotonicity -/

/-
The range of `f^[n+1]` is contained in the range of `f^[n]`.
-/
lemma iterate_range_subset (f : C → C) (n : ℕ) :
    Set.range (f^[n + 1]) ⊆ Set.range (f^[n]) := by
  intro x hx
  aesop

/-
The sequence of ranges `Set.range (f^[n])` is antitone.
-/

/-! ### Stabilization of the descending chain (Theorem A) -/

/-
**Theorem A (Range Stabilization).** For any endomorphism on a finite type,
the descending chain of iterated images stabilizes.
-/
theorem iterate_range_stabilizes (f : C → C) :
    ∃ N : ℕ, Set.range (f^[N + 1]) = Set.range (f^[N]) := by
  by_contra! h;
  -- By definition of $f^[n]$, the sequence of sets $\{ \text{range}(f^n) \}_{n \geq 0}$ is strictly decreasing.
  have h_decreasing : StrictAnti (fun n => (Set.range (f^[n]))) := by
    exact strictAnti_nat_of_succ_lt fun n => lt_of_le_of_ne ( Set.range_comp_subset_range _ _ ) ( h n );
  exact absurd ( Set.infinite_range_of_injective h_decreasing.injective ) ( Set.not_infinite.mpr <| Set.toFinite _ )

/-- The stabilization index: the smallest `N` such that the range chain stabilizes. -/
noncomputable def stabilizationIndex (f : C → C) : ℕ :=
  (iterate_range_stabilizes f).choose


/-- The **recurrent core**: the eventual stable image of `f`. -/
def recurrentCore (f : C → C) : Set C :=
  Set.range (f^[stabilizationIndex f])

/-
Once stabilized at index `N`, all subsequent iterates have the same range.
-/

/-! ### Surjectivity and bijectivity on the stable range -/

/-
On the stabilized range, `f` maps the core into itself.
-/

/-
On the stabilized range, `f` is surjective.
-/

/-
**Theorem A (Bijectivity Corollary).** On the stabilized range, `f` is bijective.
A finite surjective endomorphism is bijective.
-/

/-! ### Renormalization semigroup law (Theorem E partial) -/


/-! ### Recurrent core membership characterization -/


end FiniteTransferDynamics


