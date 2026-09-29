-- Prove2me | Theorems.Thm_DiophantineLattice_shortest_of_torsion_gap_eq
-- name    : DiophantineLattice.shortest_of_torsion_gap_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:27:48.225138+00:00
-- url     : https://prove2.me/theorems/1c3d1715-937d-41c7-948b-43ae10a68495
-- title:
--   Rigidity, hard direction.
-- statement:
--   **Rigidity, hard direction.**  If the spectral gap at an `r`-torsion shift `t` equals
--   `λ₁/r²`, then `t` is congruent modulo the lattice to `w/r` for some `w` realising the minimal
--   lattice energy.
--
--   ```lean
--   theorem DiophantineLattice.shortest_of_torsion_gap_eq{B : Matrix (Fin n) (Fin n) ℚ} {lam : ℚ} {t : Fin n → ℚ}
--       {r : ℤ} (hr : r ≠ 0) (ht : IsTorsionShift t r)
--       (hgap : IsInhomMin B t (lam / (r : ℚ) ^ 2)) :
--       ∃ w k : Fin n → ℤ, form B (emb w) = lam ∧ ∀ i, t i = (w i : ℚ) / (r : ℚ) + (k i : ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/DiophantineLatticeExactOrder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/DiophantineLatticeExactOrder.lean#L158

-- Thm stub generated from Novelty/DiophantineLatticeExactOrder.lean
import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeExactOrder
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap

/-!
# Cycle 6: spectral gaps at arbitrary torsion shifts, and the equality case

Cycles 1–2 (`Novelty/DiophantineLatticeSpectralGap.lean`,
`Novelty/DiophantineLatticeTorsionGap.lean`) computed the spectral gap of the non-homogeneous
form `x ↦ Q(x - t)` for shifts of the *special shape* `t = v/r` with `v` a shortest vector.
This file removes both restrictions and settles the equality case, i.e. it closes
Conjecture 1 of `FUTURE_DIRECTIONS.md`.

A rational point `t` is an **`r`-torsion shift** (`IsTorsionShift`) when `r • t` lies in the
lattice `L = ℤⁿ` while `t` itself does not; equivalently `t` is a nonzero `r`-torsion point of
`(L ⊗ ℚ)/L`.  For such a shift:

* `torsion_shift_gap_ge` : `Q(t - m) ≥ λ₁/r²` for **every** lattice point `m`, with no
  assumption relating `t` to a shortest vector.  (The hypothesis actually used is only
  `t ∉ L`, which is exactly what exact order `r` provides.)
* `torsion_shift_isInhomMin_iff` : the **rigidity** statement.  The bound `λ₁/r²` is attained,
  i.e. the spectral gap at `t` equals `λ₁/r²`, **iff** `t ≡ w/r (mod L)` for some `w`
  realising the minimal lattice energy `λ₁`.  So the metric quantity `μ(t)` detects the
  shortest vectors exactly.
* `shortest_of_torsion_gap_eq` / `torsion_gap_eq_of_shortest` are the two directions in
  standalone form, and `torsion_shift_no_solution` is the Diophantine corollary.
* `torsion_shift_second_gap` : the rigidity statement upgrades to a *gap in the gaps* — a
  non-extremal `r`-torsion shift has spectral gap at least `λ₂/r²`, where `λ₂` is any lower
  bound for the values of `Q` above `λ₁`.  So the spectrum of spectral gaps at `r`-torsion
  shifts has no value strictly between `λ₁/r²` and `λ₂/r²`.

The technical engine is `isInhomMin_translate`: the spectral gap depends only on the class of
`t` in `(L ⊗ ℚ)/L`, so the special shape `v/r` of cycle 2 may be assumed after a translation.

A second, small result closes the easy half of the *converse* in Conjecture 2: evenness of all
shifted theta coefficients forces the shift to lie outside `L`
(`multiplicity_even_imp_not_lattice`), because a shift *inside* `L` has the isolated
coefficient `r_t(0) = 1`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the `1/r²` law is not about shortest vectors at all — it is about
the order of the shift in `(L ⊗ ℚ)/L` — and shortest vectors are recovered exactly as the
equality case.
Experiment (Experimenter): removing `hv : Q(v) = λ₁` from `torsion_gap_ge` leaves a proof that
needs only `v - r m ≠ 0`, and `t ∉ L` gives precisely that; conversely the attainment clause
of `IsInhomMin` hands back a lattice vector `w = r t - r m` with `Q(w) = λ₁`, so the converse
is *free* once translation invariance is available.
Analysis (Analyst): the equality case is therefore a genuine "if and only if", not an
inequality with a hard converse; the earlier cycles' hypothesis "`v` is shortest" was doing no
work in the inequality and all of the work in the attainment.
Critique (Critic): `torsion_shift_isInhomMin_iff` is non-vacuous — `deepHole n` is a
`2`-torsion shift for `n ≥ 1` (`deepHole_isTorsionShift`), and the theorem applied to it
returns the cycle-3 value `n/4`.
Synthesis (PI): spectral gap `λ₁/r²` at every `r`-torsion shift, with equality exactly on the
mod-`L` classes of `w/r`, `w` shortest.
-/

open DiophantineLattice

open Finset

variable {n : ℕ}

/-! ## Torsion shifts -/




/-! ## Translation invariance of the spectral gap -/



/-! ## The spectral gap at an arbitrary torsion shift -/



/-! ## The equality case: rigidity -/

theorem DiophantineLattice.shortest_of_torsion_gap_eq{B : Matrix (Fin n) (Fin n) ℚ} {lam : ℚ} {t : Fin n → ℚ}
    {r : ℤ} (hr : r ≠ 0) (ht : IsTorsionShift t r)
    (hgap : IsInhomMin B t (lam / (r : ℚ) ^ 2)) :
    ∃ w k : Fin n → ℤ, form B (emb w) = lam ∧ ∀ i, t i = (w i : ℚ) / (r : ℚ) + (k i : ℚ) := by sorry
