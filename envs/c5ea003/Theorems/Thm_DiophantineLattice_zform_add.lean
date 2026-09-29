-- Prove2me | Theorems.Thm_DiophantineLattice_zform_add
-- name    : DiophantineLattice.zform_add
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:25:43.699125+00:00
-- url     : https://prove2.me/theorems/d497055d-d65d-4daf-b984-731b930a47a8
-- title:
--   Zform add
-- statement:
--   Formal statement of `DiophantineLattice.zform_add` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem DiophantineLattice.zform_add{B : Matrix (Fin n) (Fin n) ℤ} (hsym : ∀ i j, B i j = B j i) (x y : Fin n → ℤ) :
--       zform B (fun i => x i + y i) = zform B x + 2 * zbil B x y + zform B y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/DiophantineLatticeCharacteristic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/DiophantineLatticeCharacteristic.lean#L66

-- Thm stub generated from Novelty/DiophantineLatticeCharacteristic.lean
import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeCharacteristic
import Definitions.Def_Novelty_DiophantineLatticeCompleteSquare

/-!
# Cycle 4: characteristic vectors and the `mod 8` law behind the gap of `2`

`Novelty/DiophantineLatticeShiftedTheta.lean` proved that for `ℤⁿ` with the standard form the
shifted spectrum at the deep hole `(1/2,…,1/2)` lies in `n/4 + 2ℤ`, via the elementary fact
that a sum of `n` odd squares is `≡ n (mod 8)`.  Conjecture 3 of `FUTURE_DIRECTIONS.md` asked
for the structural reason.  This file answers it: the deep hole is `w/2` for the all-ones
vector `w`, and `w` is a **characteristic vector** of the standard form.  For an arbitrary
symmetric integral form `Q` on `ℤⁿ`:

* `characteristic_iff_dvd_eight` : `v` is characteristic (i.e. `Bil(v,u) + Q(u)` is even for
  every `u`) **iff** `Q(v + 2u) ≡ Q(v) (mod 8)` for every `u`.  So the mod-8 congruence is not
  a coincidence of `ℤⁿ` but an exact characterisation of characteristic vectors.
* `characteristic_shifted_spectrum` : consequently the shifted spectrum of the rational form at
  the half point `v/2` is contained in `Q(v)/4 + 2ℤ`, and
* `characteristic_gap_two` : distinct attained values differ by at least `2`.
* `standard_allOnes_characteristic` : the all-ones vector is characteristic for the standard
  form, so the cycle-1 result is recovered as a special case, and `sum_sq_sub_self_even`
  becomes the statement that `0` is characteristic-shifted by `w`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the `mod 8` law is equivalent to a `mod 2` condition on the linear
functional `u ↦ Bil(v,u) + Q(u)`, i.e. to `v` being characteristic; the "gap 2" phenomenon
should therefore hold for *every* lattice at the half of a characteristic vector, not just for
`ℤⁿ`.
Experiment (Experimenter): expanding `Q(v + 2u) = Q(v) + 4(Bil(v,u) + Q(u))` shows both
directions at once, since `8 ∣ 4t ↔ 2 ∣ t`.  For the standard form
`Bil(w,u) + Q(u) = Σ uᵢ(1 + uᵢ)` is visibly even, matching the enumeration in
`ComputationalEvidence.md`.
Analysis (Analyst): the factor `4` in the expansion is the same `4` as in the `λ₁/4` spectral
gap — both come from `[L : 2L]`-scaling — but the two theorems are logically independent: one
is archimedean, one is `2`-adic.  The equivalence is sharp: a non-characteristic `v` always
produces a value `≡ Q(v) + 4 (mod 8)`, breaking the gap from `2` down to `1`.
Critique (Critic): the statement is an `iff`, so it cannot be vacuous; and it is instantiated
(`standard_allOnes_characteristic`) rather than left abstract.  Positive definiteness is *not*
needed anywhere in this file — an honest hypothesis reduction relative to cycles 1–3.
Synthesis (PI): "gap 2 in the shifted theta spectrum" ⟺ "the shift is half a characteristic
vector"; the cycle-1 deep-hole theorem is the case `L = ℤⁿ`, `v = (1,…,1)`.
-/

open DiophantineLattice

open Finset

variable {n : ℕ}

/-! ## Integral forms -/

theorem DiophantineLattice.zform_add{B : Matrix (Fin n) (Fin n) ℤ} (hsym : ∀ i j, B i j = B j i) (x y : Fin n → ℤ) :
    zform B (fun i => x i + y i) = zform B x + 2 * zbil B x y + zform B y := by sorry
