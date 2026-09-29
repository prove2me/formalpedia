-- Prove2me | solution 1 for mme_recursive_yz_nonhole_implies_owned
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-12T11:04:28.75743+00:00
-- url     : https://prove2.me/submissions/34eb5cbc-3aa1-41a2-92c4-17e2cc15cb7f

import Definitions.Def_mme_recursive_yz_hash_filter
open BigOperators MME MME.RecursiveYZ MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem compatible_grade {P C W G D : Type*} [Fintype P] [Fintype C]
    (a b : P → C) (group : C → G) (boundary : C → Prop) (mu : C → W → ℕ)
    (f : P → W) (grade : W → D) (shape : G → D)
    (hf : ∀ p, grade (f p) = shape (group (a p)))
    (hu : Useful a mu f) (hc : Compatible b boundary group mu f) :
    ∀ p, grade (f p) = shape (group (b p)) := by
  classical
  intro p
  have hpos : 0 < count (group ∘ b) f (group (b p)) (f p) :=
    Finset.card_pos.mpr ⟨p, by simp⟩
  rw [hc.2] at hpos
  obtain ⟨c,hc',hpos⟩ := Finset.sum_pos_iff.mp hpos
  split_ifs at hpos with heq
  · rw [← hu c (f p)] at hpos
    obtain ⟨p',hp'⟩ := Finset.card_pos.mp hpos
    obtain ⟨hcell,hword⟩ := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hp'
    simpa only [hcell,hword,heq] using hf p'
  · omega

private theorem compatible_block {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (i : Fin 3) (a b : Address half R parent n)
    (boundary : Cell half R parent → Prop) (mu : Cell half R parent → CompleteWord ell → ℕ)
    (f : Position n → CompleteWord ell)
    (hg : Graded htotal i a f) (hu : Useful (fullCell htotal a) mu f)
    (hc : Compatible (fullCell htotal b) boundary (modeGroup i) mu f) :
    RecursiveXHash.block i b = RecursiveXHash.block i a := by
  have hgb := compatible_grade (fullCell htotal a) (fullCell htotal b) (modeGroup i)
    boundary mu f (fun w ↦ ∑ r, (w r).val) (fun g ↦ g.2.val) hg hu hc
  funext r t
  apply Fin.ext
  exact (hgb ⟨r,t,0⟩).symm.trans (hg ⟨r,t,0⟩)

theorem solution {half R ell k N p : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (S : Finset (ZMod p))
    (state : (Fin (N + 2) → ZMod p) × ZMod p)
    (address : Fin k → Address half R parent n) (hinj : Function.Injective address)
    (hT : ∀ j, address j ∈ RecursiveXHash.target m)
    (hHash : ∀ j, address j ∈ RecursiveXHash.hashed m e S state)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ)
    (i : Fin 2) (j : Fin k) (keep : (Position n → CompleteWord ell) → Prop)
    (f : Position n → CompleteWord ell)
    (hf : f ∈ unbrokenWords htotal (yzMode i) (address j) (mu (yzMode i)))
    (hn : f ∉ filterHoles htotal m e S state i (mu (yzMode i)) (address j) keep) :
    Owned htotal address mu j (yzMode i) f := by
  classical
  obtain ⟨hg,hu⟩ := by simpa only [unbrokenWords,Finset.mem_filter,Finset.mem_univ,true_and] using hf
  have hamb : ¬ ambiguous htotal m e S state i (mu (yzMode i)) (address j) f := by
    intro ha
    apply hn
    by_cases hk : keep f
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hf,hk,ha⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hf,hk⟩)
  have huniq : ∀ j', Compatible (fullCell htotal (address j')) (yzBoundary i)
      (modeGroup (yzMode i)) (mu (yzMode i)) f → j' = j := by
    intro j' hc
    by_contra hne
    apply hamb
    exact ⟨address j',hT j',compatible_block htotal (yzMode i) (address j) (address j')
      (yzBoundary i) (mu (yzMode i)) f hg hu hc,hc,fun h ↦ hne (hinj h),hHash j'⟩
  refine ⟨hg,hu,?_,?_⟩
  · intro hi
    have hi0 : i = 0 := by apply Fin.ext; change i.val = 0; have hv := congrArg Fin.val hi; change i.val + 1 = 1 at hv; omega
    subst i
    simpa only [yzBoundary, yzMode, ↓reduceIte] using huniq
  · intro hi
    have hi1 : i = 1 := by apply Fin.ext; change i.val = 1; have hv := congrArg Fin.val hi; change i.val + 1 = 2 at hv; omega
    subst i
    simpa only [yzBoundary, yzMode, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte] using huniq
