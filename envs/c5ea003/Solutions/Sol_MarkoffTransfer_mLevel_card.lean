-- Prove2me | solution 1 for MarkoffTransfer.mLevel_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:14:44.9392+00:00
-- url     : https://prove2.me/submissions/445a73d6-75df-42ab-90d2-fb10111809a3

-- Sol generated from Cryptography/MarkoffTransfer/MarkoffFreeBinary.lean
import Mathlib
import Definitions.Def_Cryptography_MarkoffTransfer_MarkoffCore
import Definitions.Def_Cryptography_MarkoffTransfer_MarkoffFreeBinary
import Theorems.Thm_MarkoffTransfer_mLevel_strict

/-!
# The Markoff Tree is a Free **Binary** Tree

The Berggren tree of primitive Pythagorean triples is a free **ternary** tree: the three
Berggren moves generate a free monoid of rank `3` (see
`Cryptography/BerggrenTrees/BerggrenFreeMonoid.lean`, `evalPair_injective`).

Here we prove the exact Markoff analogue, which is the "transfer" of that machinery to the
Markoff side — with rank `2` instead of `3`:

* `parent_childL` / `parent_childR` — **unique parent**: the descent map inverts both
  ascending Vieta moves.  This is the Markoff counterpart of `actGen_unique_parent`.
* `childL_ne_childR` — the two children of a strictly ordered node are distinct.
* `mEval_injective` — **freeness**: the evaluation of binary words at the root `(1,2,5)`
  is injective, so the Markoff tree is a free binary tree.
* `mLevel_card` — level `n` of the Markoff tree has exactly `2 ^ n` nodes.

Every node of the tree is a strictly ordered positive Markoff triple (`StrictM`), so the
whole development stays inside the Markoff surface.
-/

open MarkoffTransfer

/-! ## Strictly ordered Markoff triples -/




/-! ## The two ascending Vieta moves -/





/-! ## Children are nodes -/




/-! ## Unique parent -/

theorem parent_childL {t : ℤ × ℤ × ℤ} (h : StrictM t) : mParent (childL t) = t := by
  obtain ⟨h1, h2, h3, _, _⟩ := h
  obtain ⟨x, y, z⟩ := t
  simp only [MarkoffTransfer.childL, mParent] at *
  have hval : 3 * x * z - (3 * x * z - y) = y := by ring
  rw [hval]
  rw [if_neg (by omega)]

theorem parent_childR {t : ℤ × ℤ × ℤ} (h : StrictM t) : mParent (childR t) = t := by
  obtain ⟨h1, h2, h3, _, _⟩ := h
  obtain ⟨x, y, z⟩ := t
  simp only [MarkoffTransfer.childR, mParent] at *
  have hval : 3 * y * z - (3 * y * z - x) = x := by ring
  rw [hval]
  rw [if_pos (by omega)]

theorem parent_child {t : ℤ × ℤ × ℤ} (b : Bool) (h : StrictM t) : mParent (child b t) = t := by
  cases b
  · exact parent_childL h
  · exact parent_childR h

/-- Both ascending moves are injective on nodes. -/
theorem child_injOn (b : Bool) {s t : ℤ × ℤ × ℤ} (hs : StrictM s) (ht : StrictM t)
    (h : child b s = child b t) : s = t := by
  rw [← parent_child b hs, ← parent_child b ht, h]

/-- **The two children of a node are distinct**: the Markoff tree branches exactly twice. -/
theorem childL_ne_childR {t : ℤ × ℤ × ℤ} (h : StrictM t) : childL t ≠ childR t := by
  obtain ⟨h1, h2, h3, _, _⟩ := h
  intro hEq
  have hfst := congrArg Prod.fst hEq
  simp only [MarkoffTransfer.childL, MarkoffTransfer.childR] at hfst
  omega

/-- The images of the two ascending moves are disjoint on nodes. -/
theorem childL_ne_childR_of_nodes {s t : ℤ × ℤ × ℤ} (hs : StrictM s) (ht : StrictM t) :
    childL s ≠ childR t := by
  intro h
  have hst : s = t := by
    have h1 : mParent (childL s) = s := parent_childL hs
    have h2 : mParent (childR t) = t := parent_childR ht
    rw [← h1, ← h2, h]
  subst hst
  exact childL_ne_childR hs h

/-! ## Freeness: the tree of binary words -/






/-! ## Level counts: `2 ^ n` -/






open MarkoffTransfer in
theorem solution: ∀ n : ℕ, (mLevel n).card = 2 ^ n := by
  intro n
  induction n with
  | zero => simp [mLevel]
  | succ n ih =>
      have hL : ((mLevel n).image childL).card = 2 ^ n := by
        rw [Finset.card_image_of_injOn, ih]
        intro a ha b hb hab
        exact child_injOn false (mLevel_strict n a ha) (mLevel_strict n b hb) hab
      have hR : ((mLevel n).image childR).card = 2 ^ n := by
        rw [Finset.card_image_of_injOn, ih]
        intro a ha b hb hab
        exact child_injOn true (mLevel_strict n a ha) (mLevel_strict n b hb) hab
      have hdisj : Disjoint ((mLevel n).image childL) ((mLevel n).image childR) := by
        rw [Finset.disjoint_left]
        rintro t ht ht'
        simp only [Finset.mem_image] at ht ht'
        obtain ⟨a, ha, rfl⟩ := ht
        obtain ⟨b, hb, hbt⟩ := ht'
        exact childL_ne_childR_of_nodes (mLevel_strict n a ha) (mLevel_strict n b hb) hbt.symm
      simp only [mLevel]
      rw [Finset.card_union_of_disjoint hdisj, hL, hR]
      ring
