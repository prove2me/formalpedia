-- Prove2me | solution 1 for ToricCode.no_vertical_edge_of_min_weight
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:53:07.348476+00:00
-- url     : https://prove2.me/submissions/ed36fc53-9720-4903-bd3d-cf722cd1457a

-- Sol generated from Geometry/ToricCode/Rigidity.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_ClassWeights
import Definitions.Def_Geometry_ToricCode_Distance
import Definitions.Def_Geometry_ToricCode_Homology
import Definitions.Def_Geometry_ToricCode_Rigidity
import Theorems.Thm_ToricCode_N_le_weight_of_vWind
import Theorems.Thm_ToricCode_hWind_const
import Theorems.Thm_ToricCode_support_card_eq
import Theorems.Thm_ToricCode_winding_ne_zero_of_not_boundary
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
theorem solution(hMN : M < N) {z : Edge M N → F2}
    (hz : z ∈ cycles M N) (hnb : z ∉ boundaries M N) (hw : hammingNorm z = M)
    (x : ZMod M) (y : ZMod N) : z (true, (x, y)) = 0 := by
  classical
  have hcyc : (d1 M N) *ᵥ z = 0 := by simpa [cycles, LinearMap.mem_ker] using hz
  -- the horizontal winding must be the nonzero one
  have hh : hWind M N z 0 ≠ 0 := by
    rcases winding_ne_zero_of_not_boundary M N hz hnb with h | h
    · exact h
    · exact absurd (le_trans (N_le_weight_of_vWind M N hz h) (le_of_eq hw)) (by omega)
  set supp := Finset.univ.filter (fun e : Edge M N => z e ≠ 0) with hsupp
  have hcard : supp.card = M := by rw [hsupp, ← support_card_eq]; exact hw
  -- every column cut is met by a horizontal edge of the support
  have hcol : ∀ i : ZMod M, ∃ b : ZMod N, z (false, (i, b)) ≠ 0 := by
    intro i
    have hi : hWind M N z i ≠ 0 := by rw [hWind_const M N hcyc i]; exact hh
    by_contra hc
    push_neg at hc
    exact hi (Finset.sum_eq_zero (fun b _ => hc b))
  have hsurj : Set.SurjOn (fun e : Edge M N => e.2.1) supp (Finset.univ : Finset (ZMod M)) := by
    intro i _
    obtain ⟨b, hb⟩ := hcol i
    exact ⟨(false, (i, b)), by simp [hsupp, hb], rfl⟩
  have hinj : Set.InjOn (fun e : Edge M N => e.2.1) supp := by
    refine Finset.injOn_of_surjOn_of_card_le _ (fun e _ => Finset.mem_univ _) hsurj ?_
    rw [hcard, Finset.card_univ, ZMod.card]
  -- a vertical support edge would collide with the horizontal one in its column
  by_contra hne
  obtain ⟨b, hb⟩ := hcol x
  have h1 : ((true, (x, y)) : Edge M N) ∈ supp := by simp [hsupp, hne]
  have h2 : ((false, (x, b)) : Edge M N) ∈ supp := by simp [hsupp, hb]
  have := hinj h1 h2 rfl
  simp at this
