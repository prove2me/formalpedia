-- Prove2me | solution 1 for EmergentGeometry.weight_eq_zero_of_cutWeight_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:41:10.110644+00:00
-- url     : https://prove2.me/submissions/0efa35d2-21e6-4541-9bc9-5bfc6f22018b

-- Sol generated from Novelty/EREPRThroatCapacity.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREPRThroatCapacity
import Definitions.Def_Novelty_EmergentGeometryEntropyCone

/-!
# Throat capacity of an Einstein–Rosen bridge and the `I ≤ 2 E_W` bound

This file adds a genuinely *geometric* observable to the min-cut model of
`Novelty.EmergentGeometryEntropyCone`: the **throat capacity**

  `throat G A B = min { area(σ) : σ ⊇ A, σ ∩ B = ∅ }`,

the smallest bulk surface that has to be cut in order to disconnect the bulk
region `A` from the bulk region `B`.  Unlike the entropy `S(A)` this is *not*
constrained to be homologous to a boundary region: it measures the cross-section
of the Einstein–Rosen bridge joining `A` to `B` (the discrete analogue of the
entanglement wedge cross-section `E_W`).

Main results:

* `cutWeight_eq_zero_of_closed`, `weight_eq_zero_of_cutWeight_eq_zero`:
  a bulk surface has zero area iff no positive-weight edge crosses it.
* `throat_pos_iff_bulkPath` : **the throat capacity of a pair of cells is
  positive exactly when an Einstein–Rosen bridge joins them.**  Geometric
  connectivity is detected by a single real number.
* `mutualInfo_le_two_throat` : **`I(A:B) ≤ 2 · throat(A,B)`**, the toy-model
  form of the holographic inequality `I(A:B) ≤ 2 E_W(A:B)`: entanglement between
  two boundary regions is bounded by the cross-section of the bridge that
  connects them.  Its combinatorial engine is the new pointwise Boolean
  inequality `sepBit_split`.
* `throat_le_entropy`, `throat_sandwich` : `I(A:B)/2 ≤ throat(A,B) ≤ min(S A, S B)`.
* `ER_EPR_throat` : positive mutual information of two boundary cells forces a
  positive-capacity Einstein–Rosen bridge between them — ER = EPR with a
  quantitative bound, strengthening `bridge_of_mutualInfo_pos`.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).  In holography the entanglement wedge cross-section
`E_W` obeys `E_W ≥ I/2`.  If the slogan "ER=EPR" is to have content beyond mere
connectivity, the *width* of the bridge should bound the *amount* of
entanglement, not just its (non)vanishing.

EXPERIMENT (Experimenter).  We defined `throat` as an unconstrained min-cut and
looked for a recombination of Boolean regions realising the bound.  The winning
combination splits the minimal surface `g` of `A ∪ B` along the minimal
separating surface `σ`: `X = σ ∧ g` is homologous to `A`, `Y = ¬σ ∧ g` to `B`.
The needed pointwise fact is `sepBit_split`, i.e.
`sep(a∧b) + sep(¬a∧b) ≤ sep(b) + 2 sep(a)`, a 16-case Boolean identity; note the
factor `2` is necessary (take `a₁ = true, a₂ = false, b₁ = b₂ = true`, where the
left side is `2` and `sep b = 0`).

ANALYSIS (Analyst).  The bound is *tight*: for a single throat of weight `w`
between two boundary cells one has `throat = w` and `I = 2w`.  Combined with
`throat ≤ min(S A, S B)` we obtain a two-sided sandwich, so in the toy model the
bridge cross-section is squeezed between half the mutual information and the
entropies of its two mouths.

CRITIQUE (Critic).  `throat` is a `dite` over a possibly empty family; all
statements that use its minimality carry the disjointness hypothesis that makes
the family nonempty, and none of them is vacuous (`pairModel_throat` exhibits a
model where every hypothesis holds and the value is nonzero).
-/

noncomputable section

open EmergentGeometry

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Surfaces separating two bulk regions -/















/-! ## Monotonicity in the amount of entanglement -/



/-! ## Zero-area surfaces and bulk connectivity -/





/-! ## The bound `I(A:B) ≤ 2 · throat(A,B)` -/







/-! ## Sharpness: a single throat saturates the bound -/



open EmergentGeometry in
omit [DecidableEq V] in
theorem solution{G : BulkGraph V} {f : Region V}
    (h : cutWeight G f = 0) {x y : V} (hx : f x = true) (hy : f y = false) :
    G.weight x y = 0 := by
  have hnn : ∀ u ∈ (univ : Finset V), (0:ℝ) ≤ ∑ v, (sepBit (f u) (f v) : ℝ) * G.weight u v :=
    fun u _ => sum_nonneg fun v _ => mul_nonneg (by positivity) (G.weight_nonneg u v)
  have hsum : ∑ u, ∑ v, (sepBit (f u) (f v) : ℝ) * G.weight u v = 0 := by
    have := h
    rw [cutWeight, div_eq_zero_iff] at this
    rcases this with h' | h'
    · exact h'
    · norm_num at h'
  have hx' := (sum_eq_zero_iff_of_nonneg hnn).1 hsum x (mem_univ x)
  have hnn2 : ∀ v ∈ (univ : Finset V), (0:ℝ) ≤ (sepBit (f x) (f v) : ℝ) * G.weight x v :=
    fun v _ => mul_nonneg (by positivity) (G.weight_nonneg x v)
  have := (sum_eq_zero_iff_of_nonneg hnn2).1 hx' y (mem_univ y)
  rw [hx, hy] at this
  simpa [sepBit] using this
