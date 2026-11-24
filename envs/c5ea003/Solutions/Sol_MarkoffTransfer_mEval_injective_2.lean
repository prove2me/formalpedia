-- Prove2me | solution 2 for MarkoffTransfer.mEval_injective
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T07:15:21.525559+00:00
-- url     : https://prove2.me/submissions/4c5b40ab-0a79-4a72-83ab-d878423c67ef

-- Thm stub generated from Cryptography/MarkoffTransfer/MarkoffFreeBinary.lean
import Mathlib
import Definitions.Def_Cryptography_MarkoffTransfer_MarkoffCore
import Definitions.Def_Cryptography_MarkoffTransfer_MarkoffFreeBinary

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







/-! ## Freeness: the tree of binary words -/

namespace MarkoffTransfer

theorem isMarkoff_iff {x y z : ℤ} : IsMarkoff x y z ↔ x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z := by
  unfold IsMarkoff markoffForm; constructor <;> intro h <;> linarith

end MarkoffTransfer

namespace MarkoffTransfer

theorem markoffForm_swap₁₂ (x y z : ℤ) : markoffForm x y z = markoffForm y x z := by
  unfold markoffForm; ring

end MarkoffTransfer

namespace MarkoffTransfer

theorem markoffForm_swap₂₃ (x y z : ℤ) : markoffForm x y z = markoffForm x z y := by
  unfold markoffForm; ring

end MarkoffTransfer

namespace MarkoffTransfer

theorem IsMarkoff.swap₁₂ {x y z : ℤ} (h : IsMarkoff x y z) : IsMarkoff y x z := by
  unfold IsMarkoff at *; rw [← MarkoffTransfer.markoffForm_swap₁₂]; exact h

end MarkoffTransfer

namespace MarkoffTransfer

theorem IsMarkoff.swap₂₃ {x y z : ℤ} (h : IsMarkoff x y z) : IsMarkoff x z y := by
  unfold IsMarkoff at *; rw [← MarkoffTransfer.markoffForm_swap₂₃]; exact h

end MarkoffTransfer

namespace MarkoffTransfer

theorem IsMarkoff.swap₁₃ {x y z : ℤ} (h : IsMarkoff x y z) : IsMarkoff z y x :=
  ((h.swap₁₂).swap₂₃).swap₁₂

end MarkoffTransfer

namespace MarkoffTransfer

@[simp] theorem vieta_involutive (x y z : ℤ) : vieta x y (vieta x y z) = z := by
  unfold vieta; ring

end MarkoffTransfer

namespace MarkoffTransfer

theorem markoff_vieta {x y z : ℤ} (h : IsMarkoff x y z) : IsMarkoff x y (vieta x y z) := by
  unfold IsMarkoff markoffForm vieta at *; nlinarith [h]

end MarkoffTransfer

namespace MarkoffTransfer

theorem vieta_mul {x y z : ℤ} (h : IsMarkoff x y z) : z * vieta x y z = x ^ 2 + y ^ 2 := by
  unfold IsMarkoff markoffForm vieta at *; nlinarith [h]

end MarkoffTransfer

namespace MarkoffTransfer

theorem markoff_vieta_pos {x y z : ℤ} (h : IsMarkoff x y z) (hx : 0 < x) (hz : 0 < z) :
    0 < vieta x y z := by
  have hm := MarkoffTransfer.vieta_mul h
  nlinarith [sq_nonneg y, hx, hz]

end MarkoffTransfer

namespace MarkoffTransfer

theorem markoff_eq_one_of_top_eq_mid {x y : ℤ} (h : IsMarkoff x y y) (hx : 0 < x) (hxy : x ≤ y) :
    x = 1 ∧ y = 1 := by
  rw [MarkoffTransfer.isMarkoff_iff] at h
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have key : x ^ 2 = y ^ 2 * (3 * x - 2) := by linarith
  have hx1 : x = 1 := by nlinarith [sq_nonneg (y - x), sq_nonneg y]
  subst hx1
  exact ⟨rfl, by nlinarith [key]⟩

end MarkoffTransfer

namespace MarkoffTransfer

theorem markoff_mid_lt_top {x y z : ℤ} (h : IsMarkoff x y z) (hx : 0 < x) (hxy : x ≤ y)
    (hyz : y ≤ z) (hne : ¬(x = 1 ∧ y = 1 ∧ z = 1)) : y < z := by
  rcases lt_or_eq_of_le hyz with h' | h'
  · exact h'
  · subst h'
    obtain ⟨h1, h2⟩ := MarkoffTransfer.markoff_eq_one_of_top_eq_mid h hx hxy
    exact absurd ⟨h1, h2, h2⟩ hne

end MarkoffTransfer

namespace MarkoffTransfer

theorem markoff_descent_le {x y z : ℤ} (h : IsMarkoff x y z) (hx : 0 < x) (hxy : x ≤ y)
    (hyz : y < z) : vieta x y z ≤ y := by
  rw [MarkoffTransfer.isMarkoff_iff] at h
  have key : (y - z) * (y - vieta x y z) = x ^ 2 + 2 * y ^ 2 - 3 * x * y ^ 2 := by
    unfold vieta; nlinarith [h]
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hneg : x ^ 2 + 2 * y ^ 2 - 3 * x * y ^ 2 ≤ 0 := by nlinarith [hx, hxy, hy]
  nlinarith [key, hneg]

end MarkoffTransfer

namespace MarkoffTransfer

theorem markoff_descent_lt {x y z : ℤ} (h : IsMarkoff x y z) (hx : 0 < x) (hxy : x ≤ y)
    (hyz : y < z) : vieta x y z < z :=
  lt_of_le_of_lt (MarkoffTransfer.markoff_descent_le h hx hxy hyz) hyz

end MarkoffTransfer

namespace MarkoffTransfer

theorem MReach.swap₁₃ {x y z : ℤ} (h : MReach x y z) : MReach z y x :=
  ((h.swap₁₂).swap₂₃).swap₁₂

end MarkoffTransfer

namespace MarkoffTransfer

theorem MReach.isMarkoff {x y z : ℤ} (h : MReach x y z) : IsMarkoff x y z := by
  induction h with
  | root => rw [MarkoffTransfer.isMarkoff_iff]; norm_num
  | vieta _ ih => exact MarkoffTransfer.markoff_vieta ih
  | swap₁₂ _ ih => exact ih.swap₁₂
  | swap₂₃ _ ih => exact ih.swap₂₃

end MarkoffTransfer

namespace MarkoffTransfer

theorem MReach.pos {x y z : ℤ} (h : MReach x y z) : 0 < x ∧ 0 < y ∧ 0 < z := by
  induction h with
  | root => norm_num
  | @vieta x y z hxyz ih =>
      obtain ⟨hx, hy, hz⟩ := ih
      exact ⟨hx, hy, MarkoffTransfer.markoff_vieta_pos hxyz.isMarkoff hx hz⟩
  | swap₁₂ _ ih => exact ⟨ih.2.1, ih.1, ih.2.2⟩
  | swap₂₃ _ ih => exact ⟨ih.1, ih.2.2, ih.2.1⟩

end MarkoffTransfer

namespace MarkoffTransfer

theorem markoff_reach_ordered :
    ∀ N : ℕ, ∀ x y z : ℤ, x + y + z ≤ (N : ℤ) → 0 < x → x ≤ y → y ≤ z → IsMarkoff x y z →
      MReach x y z := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro x y z hsum hx hxy hyz hM
    by_cases hroot : x = 1 ∧ y = 1 ∧ z = 1
    · obtain ⟨h1, h2, h3⟩ := hroot; subst h1; subst h2; subst h3; exact MReach.root
    · have hylt : y < z := MarkoffTransfer.markoff_mid_lt_top hM hx hxy hyz hroot
      have hy : 0 < y := lt_of_lt_of_le hx hxy
      have hz : 0 < z := lt_trans hy hylt
      set w := vieta x y z with hw
      have hwy : w ≤ y := MarkoffTransfer.markoff_descent_le hM hx hxy hylt
      have hwpos : 0 < w := MarkoffTransfer.markoff_vieta_pos hM hx hz
      have hMw : IsMarkoff x y w := MarkoffTransfer.markoff_vieta hM
      have hNpos : 1 ≤ N := by
        have h1 : (1 : ℤ) ≤ (N : ℤ) := by omega
        exact_mod_cast h1
      have hbound : x + y + w ≤ ((N - 1 : ℕ) : ℤ) := by omega
      have hrec : MReach x y w := by
        rcases le_total w x with hcase | hcase
        · have hR : MReach w x y :=
            ih (N - 1) (by omega) w x y (by omega) hwpos hcase hxy ((hMw.swap₂₃).swap₁₂)
          exact (hR.swap₁₂).swap₂₃
        · have hR : MReach x w y :=
            ih (N - 1) (by omega) x w y (by omega) hx hcase hwy (hMw.swap₂₃)
          exact hR.swap₂₃
      have hfin := hrec.vieta
      rwa [hw, MarkoffTransfer.vieta_involutive] at hfin

end MarkoffTransfer

namespace MarkoffTransfer

theorem markoff_reach {x y z : ℤ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hM : IsMarkoff x y z) : MReach x y z := by
  have key : ∀ a b c : ℤ, 0 < a → a ≤ b → b ≤ c → IsMarkoff a b c → MReach a b c := by
    intro a b c ha hab hbc hMabc
    exact MarkoffTransfer.markoff_reach_ordered (a + b + c).toNat a b c (by omega) ha hab hbc hMabc
  rcases le_total x y with h₁ | h₁ <;> rcases le_total y z with h₂ | h₂ <;>
      rcases le_total x z with h₃ | h₃
  · exact key x y z hx h₁ h₂ hM
  · exact key x y z hx h₁ h₂ hM
  · exact (key x z y hx h₃ h₂ hM.swap₂₃).swap₂₃
  · exact ((key z x y hz h₃ h₁ ((hM.swap₁₃).swap₂₃)).swap₂₃).swap₁₃
  · exact (key y x z hy h₁ h₃ hM.swap₁₂).swap₁₂
  · exact ((key y z x hy h₂ h₃ ((hM.swap₁₂).swap₂₃)).swap₂₃).swap₁₂
  · exact (key y x z hy h₁ h₃ hM.swap₁₂).swap₁₂
  · exact (key z y x hz h₂ h₁ hM.swap₁₃).swap₁₃

end MarkoffTransfer

namespace MarkoffTransfer

theorem strictM_mRoot : StrictM mRoot := by
  refine ⟨by norm_num [mRoot], by norm_num [mRoot], by norm_num [mRoot], by norm_num [mRoot], ?_⟩
  rw [MarkoffTransfer.isMarkoff_iff]; norm_num [mRoot]

end MarkoffTransfer

namespace MarkoffTransfer

theorem StrictM.childL {t : ℤ × ℤ × ℤ} (h : StrictM t) : StrictM (childL t) := by
  obtain ⟨h1, h2, h3, h5, hM⟩ := h
  refine ⟨h1, lt_trans h2 h3, ?_, ?_, ?_⟩
  · -- `3 x z - y > z` since `x ≥ 1` and `z > y`
    simp only [MarkoffTransfer.childL]
    nlinarith [h1, h2, h3]
  · simp only [MarkoffTransfer.childL]
    nlinarith [h1, h2, h3, h5]
  · -- Markoff: from `(x, y, z)` swap to `(x, z, y)` then Vieta in the last slot
    have := MarkoffTransfer.markoff_vieta (hM.swap₂₃)
    simpa [MarkoffTransfer.childL, vieta] using this

end MarkoffTransfer

namespace MarkoffTransfer

theorem StrictM.childR {t : ℤ × ℤ × ℤ} (h : StrictM t) : StrictM (childR t) := by
  obtain ⟨h1, h2, h3, h5, hM⟩ := h
  refine ⟨lt_trans h1 h2, h3, ?_, ?_, ?_⟩
  · simp only [MarkoffTransfer.childR]
    nlinarith [h1, h2, h3]
  · simp only [MarkoffTransfer.childR]
    nlinarith [h1, h2, h3, h5]
  · have := MarkoffTransfer.markoff_vieta ((hM.swap₁₂).swap₂₃)
    simpa [MarkoffTransfer.childR, vieta] using this

end MarkoffTransfer

namespace MarkoffTransfer

theorem StrictM.child {t : ℤ × ℤ × ℤ} (b : Bool) (h : StrictM t) : StrictM (child b t) := by
  cases b
  · exact h.childL
  · exact h.childR

end MarkoffTransfer

namespace MarkoffTransfer

theorem parent_childL {t : ℤ × ℤ × ℤ} (h : StrictM t) : mParent (childL t) = t := by
  obtain ⟨h1, h2, h3, _, _⟩ := h
  obtain ⟨x, y, z⟩ := t
  simp only [MarkoffTransfer.childL, mParent] at *
  have hval : 3 * x * z - (3 * x * z - y) = y := by ring
  rw [hval]
  rw [if_neg (by omega)]

end MarkoffTransfer

namespace MarkoffTransfer

theorem parent_childR {t : ℤ × ℤ × ℤ} (h : StrictM t) : mParent (childR t) = t := by
  obtain ⟨h1, h2, h3, _, _⟩ := h
  obtain ⟨x, y, z⟩ := t
  simp only [MarkoffTransfer.childR, mParent] at *
  have hval : 3 * y * z - (3 * y * z - x) = x := by ring
  rw [hval]
  rw [if_pos (by omega)]

end MarkoffTransfer

namespace MarkoffTransfer

theorem parent_child {t : ℤ × ℤ × ℤ} (b : Bool) (h : StrictM t) : mParent (child b t) = t := by
  cases b
  · exact MarkoffTransfer.parent_childL h
  · exact MarkoffTransfer.parent_childR h

end MarkoffTransfer

namespace MarkoffTransfer

theorem child_injOn (b : Bool) {s t : ℤ × ℤ × ℤ} (hs : StrictM s) (ht : StrictM t)
    (h : child b s = child b t) : s = t := by
  rw [← MarkoffTransfer.parent_child b hs, ← MarkoffTransfer.parent_child b ht, h]

end MarkoffTransfer

namespace MarkoffTransfer

theorem childL_ne_childR {t : ℤ × ℤ × ℤ} (h : StrictM t) : childL t ≠ childR t := by
  obtain ⟨h1, h2, h3, _, _⟩ := h
  intro hEq
  have hfst := congrArg Prod.fst hEq
  simp only [MarkoffTransfer.childL, MarkoffTransfer.childR] at hfst
  omega

end MarkoffTransfer

namespace MarkoffTransfer

theorem childL_ne_childR_of_nodes {s t : ℤ × ℤ × ℤ} (hs : StrictM s) (ht : StrictM t) :
    childL s ≠ childR t := by
  intro h
  have hst : s = t := by
    have h1 : mParent (childL s) = s := MarkoffTransfer.parent_childL hs
    have h2 : mParent (childR t) = t := MarkoffTransfer.parent_childR ht
    rw [← h1, ← h2, h]
  subst hst
  exact MarkoffTransfer.childL_ne_childR hs h

end MarkoffTransfer

namespace MarkoffTransfer

theorem strictM_mEval (w : List Bool) : StrictM (mEval w) := by
  induction w with
  | nil => exact MarkoffTransfer.strictM_mRoot
  | cons b rest ih => exact ih.child b

end MarkoffTransfer

namespace MarkoffTransfer

theorem top_lt_child_top {t : ℤ × ℤ × ℤ} (b : Bool) (h : StrictM t) :
    t.2.2 < (child b t).2.2 := by
  obtain ⟨h1, h2, h3, _, _⟩ := h
  cases b <;> simp only [child, MarkoffTransfer.childL, MarkoffTransfer.childR] <;> nlinarith

end MarkoffTransfer

namespace MarkoffTransfer

theorem child_ne_mRoot {t : ℤ × ℤ × ℤ} (b : Bool) (h : StrictM t) : child b t ≠ mRoot := by
  intro hc
  have h5 : (5 : ℤ) ≤ t.2.2 := h.2.2.2.1
  have := MarkoffTransfer.top_lt_child_top b h
  rw [hc] at this
  simp only [mRoot] at this
  omega

end MarkoffTransfer

namespace MarkoffTransfer

theorem mEval_injective : Function.Injective mEval := by
  intro w₁
  induction w₁ with
  | nil =>
      intro w₂ h
      match w₂ with
      | [] => rfl
      | b :: rest => exact absurd h.symm (MarkoffTransfer.child_ne_mRoot b (MarkoffTransfer.strictM_mEval rest))
  | cons b₁ rest₁ ih =>
      intro w₂ h
      match w₂ with
      | [] => exact absurd h (MarkoffTransfer.child_ne_mRoot b₁ (MarkoffTransfer.strictM_mEval rest₁))
      | b₂ :: rest₂ =>
        have hb : b₁ = b₂ := by
          by_contra hne
          have hb' : b₂ = !b₁ := by cases b₁ <;> cases b₂ <;> simp_all
          subst hb'
          cases b₁ with
          | false =>
              exact MarkoffTransfer.childL_ne_childR_of_nodes (MarkoffTransfer.strictM_mEval rest₁) (MarkoffTransfer.strictM_mEval rest₂) h
          | true =>
              exact MarkoffTransfer.childL_ne_childR_of_nodes (MarkoffTransfer.strictM_mEval rest₂) (MarkoffTransfer.strictM_mEval rest₁) h.symm
        subst hb
        have := MarkoffTransfer.child_injOn b₁ (MarkoffTransfer.strictM_mEval rest₁) (MarkoffTransfer.strictM_mEval rest₂) h
        exact congrArg (b₁ :: ·) (ih this)

end MarkoffTransfer

namespace MarkoffTransfer

theorem mLevel_strict : ∀ (n : ℕ), ∀ t ∈ mLevel n, StrictM t := by
  intro n
  induction n with
  | zero =>
      intro t ht
      simp only [mLevel, Finset.mem_singleton] at ht
      subst ht; exact MarkoffTransfer.strictM_mRoot
  | succ n ih =>
      intro t ht
      simp only [mLevel, Finset.mem_union, Finset.mem_image] at ht
      rcases ht with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
      · exact (ih s hs).childL
      · exact (ih s hs).childR

end MarkoffTransfer

namespace MarkoffTransfer

theorem mLevel_card : ∀ n : ℕ, (mLevel n).card = 2 ^ n := by
  intro n
  induction n with
  | zero => simp [mLevel]
  | succ n ih =>
      have hL : ((mLevel n).image childL).card = 2 ^ n := by
        rw [Finset.card_image_of_injOn, ih]
        intro a ha b hb hab
        exact MarkoffTransfer.child_injOn false (MarkoffTransfer.mLevel_strict n a ha) (MarkoffTransfer.mLevel_strict n b hb) hab
      have hR : ((mLevel n).image childR).card = 2 ^ n := by
        rw [Finset.card_image_of_injOn, ih]
        intro a ha b hb hab
        exact MarkoffTransfer.child_injOn true (MarkoffTransfer.mLevel_strict n a ha) (MarkoffTransfer.mLevel_strict n b hb) hab
      have hdisj : Disjoint ((mLevel n).image childL) ((mLevel n).image childR) := by
        rw [Finset.disjoint_left]
        rintro t ht ht'
        simp only [Finset.mem_image] at ht ht'
        obtain ⟨a, ha, rfl⟩ := ht
        obtain ⟨b, hb, hbt⟩ := ht'
        exact MarkoffTransfer.childL_ne_childR_of_nodes (MarkoffTransfer.mLevel_strict n a ha) (MarkoffTransfer.mLevel_strict n b hb) hbt.symm
      simp only [mLevel]
      rw [Finset.card_union_of_disjoint hdisj, hL, hR]
      ring

end MarkoffTransfer

namespace MarkoffTransfer

theorem mLevel_isMarkoff {n : ℕ} {t : ℤ × ℤ × ℤ} (ht : t ∈ mLevel n) :
    IsMarkoff t.1 t.2.1 t.2.2 := (MarkoffTransfer.mLevel_strict n t ht).2.2.2.2

end MarkoffTransfer


theorem solution : Function.Injective mEval := by
  intro w₁
  induction w₁ with
  | nil =>
      intro w₂ h
      match w₂ with
      | [] => rfl
      | b :: rest => exact absurd h.symm (MarkoffTransfer.child_ne_mRoot b (MarkoffTransfer.strictM_mEval rest))
  | cons b₁ rest₁ ih =>
      intro w₂ h
      match w₂ with
      | [] => exact absurd h (MarkoffTransfer.child_ne_mRoot b₁ (MarkoffTransfer.strictM_mEval rest₁))
      | b₂ :: rest₂ =>
        have hb : b₁ = b₂ := by
          by_contra hne
          have hb' : b₂ = !b₁ := by cases b₁ <;> cases b₂ <;> simp_all
          subst hb'
          cases b₁ with
          | false =>
              exact MarkoffTransfer.childL_ne_childR_of_nodes (MarkoffTransfer.strictM_mEval rest₁) (MarkoffTransfer.strictM_mEval rest₂) h
          | true =>
              exact MarkoffTransfer.childL_ne_childR_of_nodes (MarkoffTransfer.strictM_mEval rest₂) (MarkoffTransfer.strictM_mEval rest₁) h.symm
        subst hb
        have := MarkoffTransfer.child_injOn b₁ (MarkoffTransfer.strictM_mEval rest₁) (MarkoffTransfer.strictM_mEval rest₂) h
        exact congrArg (b₁ :: ·) (ih this)

#print axioms solution
