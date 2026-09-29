-- Prove2me | solution 1 for VertexSplitting.splitChain_of_isSplit_aux
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T13:06:06.484893+00:00
-- url     : https://prove2.me/submissions/0f27330f-54af-4384-89c8-fa7986f4da4f

import Mathlib
import Definitions.Def_Bridges_VertexSplitting

universe u

open VertexSplitting SimpleGraph Finset in
theorem solution {E : Prop} : ∀ (n : ℕ) {V W : Type u} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {f : W → V},
    Fintype.card W - Fintype.card V ≤ n → IsSplit G H f → (E → IsProjExclusive H f) →
    SplitChain E G H f := by
  classical
  -- an injective splitting map is an isomorphism
  have base : ∀ {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W} {f : W → V},
      IsSplit G H f → Function.Injective f → SplitChain E G H f := by
    intro V W G H f hs hinj
    refine SplitChain.ofIso ⟨hinj, hs.surj⟩ fun x y => ⟨hs.adj_proj x y, fun h => ?_⟩
    obtain ⟨x', y', hx, hy, hxy⟩ := hs.cover _ _ h
    rw [hinj hx, hinj hy] at hxy
    exact hxy
  -- a non-injective splitting map peels off one single split
  have step : ∀ {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W} {f : W → V},
      IsSplit G H f → (E → IsProjExclusive H f) → ¬ Function.Injective f →
      ∃ (v : V) (A B : Set V) (g : W → V ⊕ Unit),
        (∀ x y, g x = Sum.inr () → g y = Sum.inr () → x = y) ∧ (E → ∀ u ∈ A, u ∉ B) ∧
        IsSplit G (singleSplit G v A B) (splitMap v) ∧ IsSplit (singleSplit G v A B) H g ∧
        (E → IsProjExclusive H g) ∧ f = splitMap v ∘ g := by
    intro V W G H f hs hE hni
    obtain ⟨w, w', hww', hne⟩ := Function.not_injective_iff.1 hni
    let A : Set V := {u | ∃ x z, f x = f w ∧ x ≠ w ∧ H.Adj x z ∧ f z = u}
    let B : Set V := {u | ∃ z, H.Adj w z ∧ f z = u}
    let g : W → V ⊕ Unit := fun x => if x = w then Sum.inr () else Sum.inl (f x)
    have hg_w : g w = Sum.inr () := if_pos rfl
    have hg_ne : ∀ x, x ≠ w → g x = Sum.inl (f x) := fun x hx => if_neg hx
    have hfg : ∀ x, splitMap (f w) (g x) = f x := by
      intro x
      by_cases hx : x = w
      · rw [hx, hg_w]; rfl
      · rw [hg_ne x hx]; rfl
    have hgadj : ∀ x y, H.Adj x y → (singleSplit G (f w) A B).Adj (g x) (g y) := by
      intro x y hxy
      by_cases hx : x = w <;> by_cases hy : y = w
      · rw [hx, hy] at hxy; exact (H.irrefl hxy).elim
      · rw [hx] at hxy; rw [hx, hg_w, hg_ne y hy]
        show f y ∈ B
        exact ⟨y, hxy, rfl⟩
      · rw [hy] at hxy; rw [hy, hg_w, hg_ne x hx]
        show f x ∈ B
        exact ⟨x, H.symm hxy, rfl⟩
      · rw [hg_ne x hx, hg_ne y hy]
        show G.Adj (f x) (f y) ∧ (f x = f w → f y ∈ A) ∧ (f y = f w → f x ∈ A)
        exact ⟨hs.adj_proj x y hxy, fun h => ⟨x, y, h, hx, hxy, rfl⟩,
          fun h => ⟨y, x, h, hy, H.symm hxy, rfl⟩⟩
    have hgw : ∀ x, g x = Sum.inr () → x = w := fun x hx => by
      by_contra h
      rw [hg_ne x h] at hx
      cases hx
    refine ⟨f w, A, B, g, fun x y hx hy => (hgw x hx).trans (hgw y hy).symm, ?_, ?_, ?_, ?_, ?_⟩
    · -- exclusivity of the single split
      intro e u hA hB
      obtain ⟨x, z, hx, hxw, hxz, hz⟩ := hA
      obtain ⟨z', hwz', hz'⟩ := hB
      exact hE e x w z z' hx hxw hxz hwz' (hz.trans hz'.symm)
    · -- the single split is a splitting of `G`
      refine ⟨fun u => ⟨Sum.inl u, rfl⟩, ?_, ?_, ?_⟩
      · rintro (p | ⟨⟩) (q | ⟨⟩) hpq hadj
        · have hpq' : p = q := hpq
          have hadj' : G.Adj p q := hadj.1
          rw [hpq'] at hadj'
          exact G.irrefl hadj'
        · have hpq' : p = f w := hpq
          obtain ⟨z, hwz, hz⟩ : p ∈ B := hadj
          exact hs.fiber_indep w z (by rw [hz, hpq']) hwz
        · have hpq' : f w = q := hpq
          obtain ⟨z, hwz, hz⟩ : q ∈ B := hadj
          exact hs.fiber_indep w z (by rw [hz, ← hpq']) hwz
        · exact (hadj : False).elim
      · rintro (p | ⟨⟩) (q | ⟨⟩) hadj
        · exact hadj.1
        · obtain ⟨z, hwz, hz⟩ : p ∈ B := hadj
          have := hs.adj_proj w z hwz
          rw [hz] at this
          exact this.symm
        · obtain ⟨z, hwz, hz⟩ : q ∈ B := hadj
          have := hs.adj_proj w z hwz
          rw [hz] at this
          exact this
        · exact (hadj : False).elim
      · intro p q hpq
        obtain ⟨x, y, hx, hy, hxy⟩ := hs.cover p q hpq
        exact ⟨g x, g y, by rw [hfg, hx], by rw [hfg, hy], hgadj x y hxy⟩
    · -- `H` is a splitting of the single split
      refine ⟨?_, ?_, hgadj, ?_⟩
      · rintro (u | ⟨⟩)
        · by_cases hu : u = f w
          · exact ⟨w', by rw [hg_ne w' (Ne.symm hne), ← hww', hu]⟩
          · obtain ⟨x, hx⟩ := hs.surj u
            have hxw : x ≠ w := fun h => hu (by rw [← hx, h])
            exact ⟨x, by rw [hg_ne x hxw, hx]⟩
        · exact ⟨w, hg_w⟩
      · intro x y hxy hadj
        by_cases hx : x = w <;> by_cases hy : y = w
        · rw [hx, hy] at hadj; exact H.irrefl hadj
        · rw [hx, hg_w, hg_ne y hy] at hxy; cases hxy
        · rw [hy, hg_w, hg_ne x hx] at hxy; cases hxy
        · rw [hg_ne x hx, hg_ne y hy] at hxy
          exact hs.fiber_indep x y (Sum.inl_injective hxy) hadj
      · rintro (p | ⟨⟩) (q | ⟨⟩) hab
        · have hab' : G.Adj p q ∧ (p = f w → q ∈ A) ∧ (q = f w → p ∈ A) := hab
          obtain ⟨hpq, hpA, hqA⟩ := hab'
          by_cases hp : p = f w
          · have hq : q ≠ f w := fun h => by
              rw [h, ← hp] at hpq
              exact G.irrefl hpq
            obtain ⟨x, z, hx, hxw, hxz, hz⟩ := hpA hp
            have hzw : z ≠ w := fun h => hq (by rw [← hz, h])
            exact ⟨x, z, by rw [hg_ne x hxw, hx, hp], by rw [hg_ne z hzw, hz], hxz⟩
          · by_cases hq : q = f w
            · obtain ⟨x, z, hx, hxw, hxz, hz⟩ := hqA hq
              have hzw : z ≠ w := fun h => hp (by rw [← hz, h])
              exact ⟨z, x, by rw [hg_ne z hzw, hz], by rw [hg_ne x hxw, hx, hq], H.symm hxz⟩
            · obtain ⟨x, y, hx, hy, hxy⟩ := hs.cover p q hpq
              have hxw : x ≠ w := fun h => hp (by rw [← hx, h])
              have hyw : y ≠ w := fun h => hq (by rw [← hy, h])
              exact ⟨x, y, by rw [hg_ne x hxw, hx], by rw [hg_ne y hyw, hy], hxy⟩
        · obtain ⟨z, hwz, hz⟩ : p ∈ B := hab
          exact ⟨z, w, by rw [hg_ne z (H.ne_of_adj hwz).symm, hz], hg_w, H.symm hwz⟩
        · obtain ⟨z, hwz, hz⟩ : q ∈ B := hab
          exact ⟨w, z, hg_w, by rw [hg_ne z (H.ne_of_adj hwz).symm, hz], hwz⟩
        · exact (hab : False).elim
    · -- projection-exclusivity is inherited
      intro e x y z z' hxy hne' hxz hyz' hzz'
      exact hE e x y z z' (by rw [← hfg x, ← hfg y, hxy]) hne' hxz hyz'
        (by rw [← hfg z, ← hfg z', hzz'])
    · funext x
      exact (hfg x).symm
  intro n
  induction n with
  | zero =>
    intro V W _ _ G H f hn hs _
    apply base hs
    by_contra hni
    have := Fintype.card_lt_of_surjective_not_injective f hs.surj hni
    omega
  | succ k ih =>
    intro V W _ _ G H f hn hs hE
    by_cases hinj : Function.Injective f
    · exact base hs hinj
    obtain ⟨v, A, B, g, hnew, hdisj, hsplit, hs', hE', hf⟩ := step hs hE hinj
    refine SplitChain.step v A B g hnew hdisj hsplit (ih ?_ hs' hE') hf
    rw [Fintype.card_sum, Fintype.card_unit]
    omega
