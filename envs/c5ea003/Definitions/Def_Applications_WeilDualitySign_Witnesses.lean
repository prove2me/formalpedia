-- Prove2me | Definitions.Def_Applications_WeilDualitySign_Witnesses
-- name    : Applications_WeilDualitySign_Witnesses
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:58:59.6507+00:00
-- url     : https://prove2.me/theorems/a57e66ce-f819-450a-a38c-12c0fc478eae
-- title:
--   Aether Catalog definitions — Applications_WeilDualitySign_Witnesses
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.WeilDualitySign.Witnesses`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/WeilDualitySign/Witnesses.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_WeilDualitySign_EigenvalueModel
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sharpness Witnesses for the Duality Sign Law

This file is the adversarial half of `EigenvalueModel.lean`.  There we proved

  `∏ α_i = (−1)^{#neg-fixed} · Q^d`,   `ε = (−1)^{d + #neg-fixed}`,

and the mission conjecture as the corollary "no `−Q` fixed point ⟹ `∏ α_i = Q^d`,
`ε = (−1)^d`".  Here we exhibit explicit complex eigensystems showing that **every
hypothesis is load-bearing and the theorem is sharp**:

* `posFixed_deg_one` — degree 1 with the fixed point `α = +Q`: `∏ α = Q`, `ε = −1`.
  This is the `d = 1` sign the conjecture predicts.
* `negFixed_deg_one` — degree 1 with the fixed point `α = −Q`: `∏ α = −Q ≠ Q` and
  `ε = +1 ≠ (−1)^1`.  A *single* anti-diagonal fixed point flips the sign, so the
  hypothesis of the conjecture cannot be deleted.
* `pair_deg_two` — a free duality 2-cycle `{a, Q²/a}`: `∏ α = Q²`, `ε = +1`, valid for
  every `a ≠ 0`.  2-cycles are sign-neutral, whatever the eigenvalues are.
* `twoNegFixed_deg_two` — two `−Q` fixed points: the hypothesis of the conjecture
  *fails* yet the conclusion `∏ α = Q²` still *holds*.  The hypothesis is therefore
  sufficient but not necessary — only the parity matters.
* `cycle4_two_pairs` and `cycle4_mixed` — the degree-4 witnesses: two duality
  2-cycles give `ε = +1 = (−1)^4`, while `(+Q, −Q, a, Q²/a)` gives `ε = −1 ≠ (−1)^4`.
* `three_cycle_no_fixed_point_sign_flip` — the deepest one: a *non-involutive* duality
  (a 3-cycle) with **no fixed points at all** — so the mission hypothesis holds
  vacuously — yet `∏ α = −Q³`.  Involutivity of `σ` is not decorative: it is exactly
  what the pairing argument consumes.

-- !-- Lab Notes -- !--
Experiment (Experimenter): the search for a counterexample to the conjecture was run
  by hand over all duality structures of degree ≤ 4 (`ε` depends only on `d` and the
  fixed-point data, so degree 4 already exhibits every pattern: 4 fixed points,
  2 fixed + one 2-cycle, two 2-cycles).  All conform to `ε = (−1)^{d + #neg-fixed}`.
Analysis (Analyst): the only way to break the conclusion while keeping the stated
  hypothesis is to break *involutivity*.  Chasing `α_i α_{σ i} = Q²` around a 3-cycle
  forces `α_0 = α_2` and then `α_0² = Q²`, so the whole cycle is constant `±Q`; the
  choice `−Q` yields `∏ α = −Q³` with an empty fixed-point set.
Critique (Critic): all witnesses are genuine inhabitants of `DualEigensystem` (the
  3-cycle one is stated separately, precisely because it is not one), and each claim
  is an equation between explicit complex numbers, not a vacuous implication.
-/

open Finset

namespace WeilDualitySign

namespace Witnesses

variable (Q : ℂ) (hQ : Q ≠ 0)

/-! ### Degree 1: the two self-dual eigenvalues -/

/-- Degree-1 system with the **`+Q` fixed point** (`σ = id`, `α = Q`). -/
def posFixed : DualEigensystem ℂ (Fin 1) where
  Q := Q
  Q_ne_zero := hQ
  α := fun _ => Q
  σ := Equiv.refl _
  σ_involutive := fun _ => rfl
  duality := fun _ => by ring

/-- Degree-1 system with the **`−Q` fixed point** (`σ = id`, `α = −Q`). -/
def negFixedOne : DualEigensystem ℂ (Fin 1) where
  Q := Q
  Q_ne_zero := hQ
  α := fun _ => -Q
  σ := Equiv.refl _
  σ_involutive := fun _ => rfl
  duality := fun _ => by ring



/-! ### Degree 2: a free duality pair, and two anti-diagonal fixed points -/

/-- Degree-2 system consisting of a single duality 2-cycle `{a, Q²/a}`. -/
noncomputable def pair (a : ℂ) (ha : a ≠ 0) : DualEigensystem ℂ (Fin 2) where
  Q := Q
  Q_ne_zero := hQ
  α := ![a, Q ^ 2 / a]
  σ := Equiv.swap 0 1
  σ_involutive := by decide
  duality := by
    intro i
    fin_cases i <;>
      simp [Equiv.swap_apply_left, Equiv.swap_apply_right] <;> field_simp


/-- Degree-2 system with **two** `−Q` fixed points (`σ = id`, `α ≡ −Q`). -/
def twoNegFixed : DualEigensystem ℂ (Fin 2) where
  Q := Q
  Q_ne_zero := hQ
  α := fun _ => -Q
  σ := Equiv.refl _
  σ_involutive := fun _ => rfl
  duality := fun _ => by ring


/-! ### Degree 4: the cycle-4 witnesses -/

/-- Degree-4 system built from **two** duality 2-cycles `{a, Q²/a}`, `{b, Q²/b}`. -/
noncomputable def twoPairs (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    DualEigensystem ℂ (Fin 4) where
  Q := Q
  Q_ne_zero := hQ
  α := ![a, Q ^ 2 / a, b, Q ^ 2 / b]
  σ := Equiv.swap 0 1 * Equiv.swap 2 3
  σ_involutive := by decide
  duality := by
    intro i
    fin_cases i <;>
      simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> field_simp


/-- Degree-4 system mixing the two fixed points `+Q`, `−Q` with one duality pair. -/
noncomputable def mixed (a : ℂ) (ha : a ≠ 0) : DualEigensystem ℂ (Fin 4) where
  Q := Q
  Q_ne_zero := hQ
  α := ![Q, -Q, a, Q ^ 2 / a]
  σ := Equiv.swap 2 3
  σ_involutive := by decide
  duality := by
    intro i
    fin_cases i <;>
      simp [Equiv.swap_apply_def] <;> field_simp


/-! ### Involutivity is essential: a fixed-point-free 3-cycle with `∏ α = −Q³` -/


end Witnesses

end WeilDualitySign


