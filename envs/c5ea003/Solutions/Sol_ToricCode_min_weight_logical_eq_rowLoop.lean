-- Prove2me | solution 1 for ToricCode.min_weight_logical_eq_rowLoop
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T12:55:23.769687+00:00
-- url     : https://prove2.me/submissions/2cbab38c-63c4-40b7-8b6e-57c800c19d71

-- Sol generated from Geometry/ToricCode/Rigidity.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_ClassWeights
import Definitions.Def_Geometry_ToricCode_Homology
import Definitions.Def_Geometry_ToricCode_Rigidity
import Theorems.Thm_ToricCode_no_vertical_edge_of_min_weight
import Theorems.Thm_ToricCode_support_card_eq
import Theorems.Thm_ToricCode_zmod_const_of_succ
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

lemma F2_eq_one_of_ne_zero {a : F2} (h : a ≠ 0) : a = 1 := by
  revert h
  revert a
  decide



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
    (hz : z ∈ cycles M N) (hnb : z ∉ boundaries M N) (hw : hammingNorm z = M) :
    ∃ y : ZMod N, z = rowLoop M N y := by
  classical
  have hcyc : (d1 M N) *ᵥ z = 0 := by simpa [cycles, LinearMap.mem_ker] using hz
  have hvert : ∀ (x : ZMod M) (y : ZMod N), z (true, (x, y)) = 0 :=
    no_vertical_edge_of_min_weight hMN hz hnb hw
  -- a purely horizontal cycle is constant along each row
  have hstep : ∀ (x : ZMod M) (y : ZMod N),
      z (false, (x + 1, y)) = z (false, (x, y)) := by
    intro x y
    have h := congrFun hcyc (x + 1, y)
    rw [d1_mulVec] at h
    have e1 : ((x + 1, y) : ZMod M × ZMod N) - (1, 0) = (x, y) := by
      simp only [Prod.mk_sub_mk, Prod.mk.injEq]
      constructor <;> ring
    have e2 : ((x + 1, y) : ZMod M × ZMod N) - (0, 1) = (x + 1, y - 1) := by simp
    rw [e1, e2, hvert, hvert, add_zero, add_zero] at h
    have h2 : ∀ a c : F2, a + c = 0 → a = c := by decide
    exact h2 _ _ h
  have hconst : ∀ (x : ZMod M) (y : ZMod N), z (false, (x, y)) = z (false, (0, y)) := by
    intro x y
    exact zmod_const_of_succ (fun x => z (false, (x, y))) (fun x => hstep x y) x
  -- count the occupied rows
  set T := Finset.univ.filter (fun y : ZMod N => z (false, (0, y)) ≠ 0) with hT
  have himg : (Finset.univ.filter (fun e : Edge M N => z e ≠ 0))
      = (Finset.univ ×ˢ T).image (fun p : ZMod M × ZMod N => ((false, p) : Edge M N)) := by
    ext e
    obtain ⟨b, x, y⟩ := e
    constructor
    · intro hmem
      have hne : z (b, (x, y)) ≠ 0 := by simpa using hmem
      cases b
      · refine Finset.mem_image.mpr ⟨(x, y), ?_, rfl⟩
        simp only [Finset.mem_product, Finset.mem_univ, true_and, hT, Finset.mem_filter]
        rw [← hconst x y]
        exact hne
      · exact absurd (hvert x y) hne
    · intro hmem
      obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp hmem
      obtain ⟨a, c⟩ := p
      have hc : z (false, (0, c)) ≠ 0 := by
        have h2 := (Finset.mem_product.mp hp).2
        simpa [hT] using h2
      simp only [Prod.mk.injEq] at hpe
      obtain ⟨rfl, rfl, rfl⟩ := hpe
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hconst a c]
      exact hc
  have hinj : Function.Injective (fun p : ZMod M × ZMod N => ((false, p) : Edge M N)) :=
    fun a b hab => by simpa using hab
  have hcard : M * T.card = M := by
    have := hw
    rw [support_card_eq, himg, Finset.card_image_of_injective _ hinj,
      Finset.card_product, Finset.card_univ, ZMod.card] at this
    exact this
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hT1 : T.card = 1 :=
    Nat.eq_of_mul_eq_mul_left hM (by rw [hcard, mul_one])
  obtain ⟨y₀, hy₀⟩ := Finset.card_eq_one.mp hT1
  refine ⟨y₀, ?_⟩
  funext e
  obtain ⟨b, x, y⟩ := e
  have hyT : ∀ y : ZMod N, z (false, (0, y)) ≠ 0 ↔ y = y₀ := by
    intro y
    constructor
    · intro h
      have : y ∈ T := by simp [hT, h]
      rw [hy₀] at this
      simpa using this
    · intro hy
      have hmem : y₀ ∈ T := by rw [hy₀]; simp
      rw [hy]
      simpa [hT] using hmem
  cases b
  · rw [hconst x y]
    by_cases h : y = y₀
    · subst h
      rw [show rowLoop M N y ((false, (x, y)) : Edge M N) = 1 by simp [rowLoop]]
      exact F2_eq_one_of_ne_zero ((hyT y).mpr rfl)
    · rw [show rowLoop M N y₀ ((false, (x, y)) : Edge M N) = 0 by simp [rowLoop, h]]
      by_contra hc
      exact h ((hyT y).mp hc)
  · rw [hvert x y, show rowLoop M N y₀ ((true, (x, y)) : Edge M N) = 0 by simp [rowLoop]]
