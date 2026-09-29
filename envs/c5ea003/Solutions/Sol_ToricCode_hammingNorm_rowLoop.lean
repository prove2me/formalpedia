-- Prove2me | solution 1 for ToricCode.hammingNorm_rowLoop
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T12:52:12.145501+00:00
-- url     : https://prove2.me/submissions/d9395125-fa2f-45ca-90c1-57cb38c18468

-- Sol generated from Geometry/ToricCode/Rigidity.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_ClassWeights
import Definitions.Def_Geometry_ToricCode_Rigidity
import Theorems.Thm_ToricCode_support_card_eq
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






omit [NeZero M] [NeZero N] in
/-- The support of a row loop is exactly the set of horizontal edges of that row. -/
lemma rowLoop_ne_zero_iff (y : ZMod N) (e : Edge M N) :
    rowLoop M N y e ≠ 0 ↔ (e.1 = false ∧ e.2.2 = y) := by
  simp only [rowLoop]
  by_cases h : e.1 = false ∧ e.2.2 = y <;> simp [h]


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
theorem solution(y : ZMod N) : hammingNorm (rowLoop M N y) = M := by
  classical
  rw [support_card_eq]
  have hinj : Function.Injective (fun x : ZMod M => ((false, (x, y)) : Edge M N)) :=
    fun a b hab => by simpa using congrArg (fun e : Edge M N => e.2.1) hab
  have himg : (Finset.univ.filter (fun e : Edge M N => rowLoop M N y e ≠ 0))
      = Finset.univ.image (fun x : ZMod M => ((false, (x, y)) : Edge M N)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      rowLoop_ne_zero_iff]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨b, x, w⟩ := e
      exact ⟨x, by simp_all⟩
    · rintro ⟨x, rfl⟩
      exact ⟨rfl, rfl⟩
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]
