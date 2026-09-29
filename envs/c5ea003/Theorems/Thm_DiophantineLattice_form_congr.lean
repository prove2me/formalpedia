-- Prove2me | Theorems.Thm_DiophantineLattice_form_congr
-- name    : DiophantineLattice.form_congr
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:26:24.622101+00:00
-- url     : https://prove2.me/theorems/6535bb28-f3d9-40f9-883e-1bb4e3e5f762
-- title:
--   Congruence identity.
-- statement:
--   **Congruence identity.**  Changing coordinates by `U` replaces the Gram matrix `B` by
--   `Uᵀ B U`.
--
--   ```lean
--   theorem DiophantineLattice.form_congr(B U : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
--       form (Uᵀ * B * U) x = form B (U *ᵥ x) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/DiophantineLatticeReduction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/DiophantineLatticeReduction.lean#L62

-- Thm stub generated from Novelty/DiophantineLatticeReduction.lean
import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeCharacteristic
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap

/-!
# Cycle 5: lattice reduction — the spectral gap is a `GL_n(ℤ)`-invariant

All the invariants of the previous cycles (`IsMinEnergy`, `IsInhomMin`, hence the spectral gap
`λ₁/r²` and the covering radius) were defined through a *coordinate* description of the lattice
`ℤⁿ` together with a Gram matrix `B`.  Lattice reduction changes the basis by a unimodular
matrix `U`, which replaces `B` by the congruent matrix `Uᵀ B U`.  This file proves that nothing
in the theory depends on that choice:

* `form_congr` : `Q_{UᵀBU}(x) = Q_B(U x)` for arbitrary matrices — the congruence identity;
* `isMinEnergy_congr` : the minimal lattice energy is unchanged by a unimodular change of
  basis;
* `isInhomMin_congr` : the spectral gap at a shift `t` equals the spectral gap of the
  congruent form at `U t`;
* `covering_ge_quarter_min_congr` : consequently the packing–covering inequality is a statement
  about the lattice, not about a chosen basis.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the `λ₁/r²` gap should be an isometry invariant of the lattice; if
it were not, the whole programme would be an artefact of coordinates.
Experiment (Experimenter): the congruence identity reduces to a four-fold sum interchange
(`sum4_comm`); the lattice transfer then needs only that `m ↦ U m` is a bijection of `ℤⁿ`,
which follows from `V U = 1` and `U V = 1` — no positivity, no reduction theory.
Analysis (Analyst): the two hypotheses `U V = 1` and `V U = 1` are exactly unimodularity;
the transfer of `IsInhomMin` moves the shift as `t ↦ U t`, so half-lattice points are carried to
half-lattice points, i.e. the cycle-1 and cycle-4 theorems are basis-independent as well.
Critique (Critic): the invariance is stated as an `iff`, so both directions are proved; the
congruence lemma holds for *arbitrary* `U` (not just unimodular), isolating exactly where
unimodularity is needed.
Synthesis (PI): every spectral quantity in this project is a `GL_n(ℤ)`-invariant of the pair
(lattice, quadratic form), which is what makes "lattice reduction" a legitimate tool for
computing it.
-/

open DiophantineLattice

open Finset Matrix

variable {n : ℕ}

theorem DiophantineLattice.form_congr(B U : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    form (Uᵀ * B * U) x = form B (U *ᵥ x) := by sorry
