-- Prove2me | Theorems.Thm_DiophantineLattice_isMinEnergy_congr
-- name    : DiophantineLattice.isMinEnergy_congr
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:27:28.314423+00:00
-- url     : https://prove2.me/theorems/2293d40d-bb42-43d8-a37d-73e81741b20b
-- title:
--   The minimal lattice energy is invariant under a unimodular change of basis.
-- statement:
--   The minimal lattice energy is invariant under a unimodular change of basis.
--
--   ```lean
--   theorem DiophantineLattice.isMinEnergy_congr(hUV : U * V = 1) (hVU : V * U = 1)
--       (B : Matrix (Fin n) (Fin n) ℚ) (lam : ℚ) :
--       IsMinEnergy ((toRat U)ᵀ * B * (toRat U)) lam ↔ IsMinEnergy B lam := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/DiophantineLatticeReduction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/DiophantineLatticeReduction.lean#L102

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





/-! ## Unimodular transfer -/

variable {U V : Matrix (Fin n) (Fin n) ℤ}

theorem DiophantineLattice.isMinEnergy_congr(hUV : U * V = 1) (hVU : V * U = 1)
    (B : Matrix (Fin n) (Fin n) ℚ) (lam : ℚ) :
    IsMinEnergy ((toRat U)ᵀ * B * (toRat U)) lam ↔ IsMinEnergy B lam := by sorry
