-- Prove2me | solution 1 for DiophantineLattice.form_congr
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:29:12.762188+00:00
-- url     : https://prove2.me/submissions/cb81b015-7c46-48df-8e16-0d00f9950d25

-- Sol generated from Novelty/DiophantineLatticeReduction.lean
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

/-- A four-fold interchange of summation. -/
lemma sum4_comm (f : Fin n → Fin n → Fin n → Fin n → ℚ) :
    ∑ k, ∑ l, ∑ i, ∑ j, f i j k l = ∑ i, ∑ j, ∑ k, ∑ l, f i j k l := by
  calc ∑ k, ∑ l, ∑ i, ∑ j, f i j k l = ∑ k, ∑ i, ∑ l, ∑ j, f i j k l :=
        sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ l, ∑ j, f i j k l := Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ j, ∑ l, f i j k l :=
        sum_congr rfl fun i _ => sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, ∑ l, f i j k l :=
        sum_congr rfl fun i _ => Finset.sum_comm

lemma mulVec_apply' (M : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ) (i : Fin n) :
    (M *ᵥ v) i = ∑ j, M i j * v j := by
  simp [Matrix.mulVec, dotProduct]

lemma conj_apply (B U : Matrix (Fin n) (Fin n) ℚ) (k l : Fin n) :
    (Uᵀ * B * U) k l = ∑ i, ∑ j, U i k * B i j * U j l := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]


/-! ## Unimodular transfer -/

variable {U V : Matrix (Fin n) (Fin n) ℤ}








open DiophantineLattice in
theorem solution(B U : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    form (Uᵀ * B * U) x = form B (U *ᵥ x) := by
  have hL : form (Uᵀ * B * U) x
      = ∑ k, ∑ l, ∑ i, ∑ j, U i k * B i j * U j l * x k * x l := by
    simp only [form, bil, conj_apply, Finset.sum_mul]
  have hR : form B (U *ᵥ x)
      = ∑ i, ∑ j, ∑ k, ∑ l, U i k * B i j * U j l * x k * x l := by
    have hstep : ∀ (a : ℚ) (f g : Fin n → ℚ),
        a * (∑ k, f k) * (∑ l, g l) = ∑ k, ∑ l, a * f k * g l := by
      intro a f g
      rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
      exact sum_congr rfl fun k _ => by
        rw [Finset.mul_sum]; exact sum_congr rfl fun l _ => by ring
    simp only [form, bil]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [mulVec_apply', mulVec_apply', hstep]
    exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring
  rw [hL, hR, sum4_comm]
