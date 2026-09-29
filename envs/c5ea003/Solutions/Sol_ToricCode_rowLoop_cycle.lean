-- Prove2me | solution 1 for ToricCode.rowLoop_cycle
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:53:08.680055+00:00
-- url     : https://prove2.me/submissions/85c36e52-cdf4-41c2-a073-ae9f7df6e722

-- Sol generated from Geometry/ToricCode/Rigidity.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_ClassWeights
import Definitions.Def_Geometry_ToricCode_Rigidity
/-!
# Rigidity of minimum-weight logical operators

`ToricCode.toric_distance` computes the *value* `min M N` of the `Z`-distance.
This file classifies the *optimisers*: for a strictly rectangular torus
(`M < N`) a logical operator of the minimal weight `M` is **exactly** one of the
`N` horizontal row loops — no other chain achieves the distance.

* `rowLoop y` — all `M` horizontal edges of the row at height `y`;
* `rowLoop_is_logical` / `hammingNorm_rowLoop` — each row loop is a logical
  operator of weight `M`;
* `min_weight_logical_eq_rowLoop` — the converse, i.e. rigidity;
* `min_weight_logicals_card` — consequently the minimum-weight logical operators
  are in bijection with `ZMod N`: there are exactly `N` of them.

The proof is a counting rigidity argument.  A cycle with nonzero horizontal
winding meets each of the `M` disjoint column cuts, so weight `M` forces the
support to meet each cut *exactly once* and to contain **no vertical edge at
all**.  A purely horizontal cycle satisfies `z(false, u) = z(false, u - (1,0))`,
so its indicator is constant along each row; counting the support again then
forces exactly one row to be occupied.
-/

open Matrix

open ToricCode

variable (M N : ℕ) [NeZero M] [NeZero N]




variable {M N}








/-! ### Rigidity -/





/-
-- !-- Lab Notes -- !--

Hypothesis (Hypothesizer).
  `toric_distance` computes the *value* of the systole; the bolder claim is that
  the optimisers are rigid, i.e. that a shortest noncontractible cellular loop on
  a strictly rectangular torus must literally be a straight row.

Experiment (Experimenter).
  Exhaustive enumeration over all `2^(2MN)` one-chains, using the definitions of
  this directory, counting the logical operators of the minimal weight
  `min M N` and comparing them with the `N` row loops `rowLoop`:

    M=1 N=2 :  #minimum-weight logicals = 2,  #row loops = 2,  equal
    M=1 N=3 :  #minimum-weight logicals = 3,  #row loops = 3,  equal
    M=2 N=3 :  #minimum-weight logicals = 3,  #row loops = 3,  equal
    M=2 N=2 :  #minimum-weight logicals = 4,  #row loops = 2,  NOT equal

  The last line is the decisive datum: it shows the hypothesis `M < N` is not a
  proof artefact.  On the square torus the `L` column loops also attain the
  distance, so there are `2L` optimisers and the classification statement is
  false as literally phrased.

Analysis (Analyst).
  The proof is a two-step counting rigidity.  (i) Weight `M` plus nonzero
  horizontal winding forces the support to meet each of the `M` column cuts, and
  since `|support| = M` the column map is a *bijection* on the support
  (`Finset.injOn_of_surjOn_of_card_le`); a vertical support edge would then
  collide with the horizontal edge in its own column, so there is none.
  (ii) A purely horizontal cycle satisfies `z(false,u) = z(false,u-(1,0))`, hence
  is constant along rows, so the support is a union of complete rows; `M·|T| = M`
  leaves exactly one row.  Note that step (i) is where `M < N` enters — it is
  needed only to rule out the *vertical* winding, via `N ≤ weight = M`.

Critique (Critic).
  The statement is not vacuous: `rowLoop_is_logical` and `hammingNorm_rowLoop`
  exhibit `N` distinct witnesses, and `min_weight_logicals_card` is an equality
  of sets, not an inequality.  No `native_decide` is used; the two `decide` calls
  are on closed identities in `𝔽₂`.

----
-/
open ToricCode in
theorem solution(y : ZMod N) : (d1 M N) *ᵥ (rowLoop M N y) = 0 := by
  funext v
  rw [d1_mulVec]
  obtain ⟨a, b⟩ := v
  simp only [rowLoop]
  have e1 : ((a, b) : ZMod M × ZMod N) - (1, 0) = (a - 1, b) := by simp
  have e2 : ((a, b) : ZMod M × ZMod N) - (0, 1) = (a, b - 1) := by simp
  rw [e1, e2]
  by_cases h : b = y
  · simp [h]
    decide
  · simp [h]
