-- Prove2me | solution 1 for CWorldFiltration.representable_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T17:40:42.116996+00:00
-- url     : https://prove2.me/submissions/51544a69-ae8e-4f31-85d8-8364cbf4c4e9

import Mathlib
import Definitions.Def_Speculative_AutoResearch_CWorldFiltration

open CWorldFiltration Function in
theorem solution (P : Type*) [Preorder P] [Fintype P] [Nonempty P] :
    Representable P ↔
      ((∃ r : P, ∀ p, r ≤ p) ∧ (∀ x y : P, ∃ z, x ≤ z ∧ y ≤ z) ∧
        ∀ p q : P, p ≤ q → q ≤ p → p = q) := by
  classical
  constructor
  · rintro ⟨n, m, f, hf⟩
    obtain ⟨p0⟩ := (inferInstance : Nonempty P)
    obtain ⟨w0, -⟩ := hf p0
    have hn : 0 < n := Fin.pos w0.clock
    let bot : CWorld (Fin n) (Fin m) := ⟨⟨0, hn⟩, fun _ => false⟩
    let top : CWorld (Fin n) (Fin m) := ⟨⟨n - 1, by omega⟩, fun _ => true⟩
    have hbot : ∀ w : CWorld (Fin n) (Fin m), bot ≤ w := by
      intro w
      refine ⟨?_, fun b hb => by simp [bot] at hb⟩
      rw [Fin.le_def]
      exact Nat.zero_le _
    have htop : ∀ w : CWorld (Fin n) (Fin m), w ≤ top := by
      intro w
      refine ⟨?_, fun b _ => rfl⟩
      rw [Fin.le_def]
      have := w.clock.isLt
      show (w.clock : ℕ) ≤ n - 1
      omega
    refine ⟨⟨f.toFun bot, fun p => ?_⟩, fun x y => ?_, fun p q hpq hqp => ?_⟩
    · obtain ⟨w, rfl⟩ := hf p
      exact f.forth (hbot w)
    · obtain ⟨wx, rfl⟩ := hf x
      obtain ⟨wy, rfl⟩ := hf y
      exact ⟨f.toFun top, f.forth (htop wx), f.forth (htop wy)⟩
    · -- a maximal preimage of `p`, pushed up by the back condition
      by_contra hne
      have hA : (Finset.univ.filter fun w => f.toFun w = p).Nonempty := by
        obtain ⟨w, hw⟩ := hf p
        exact ⟨w, by simp [hw]⟩
      obtain ⟨w, hwmax⟩ := Finset.exists_maximal hA
      have hwp : f.toFun w = p := by simpa using hwmax.1
      obtain ⟨y, hwy, hyq⟩ := f.back w q (hwp ▸ hpq)
      obtain ⟨z, hyz, hzp⟩ := f.back y p (hyq ▸ hqp)
      have hzA : z ∈ Finset.univ.filter fun w => f.toFun w = p := by simp [hzp]
      have hzw : z ≤ w := hwmax.2 hzA (hwy.trans hyz)
      have hyw : y = w := le_antisymm (hyz.trans hzw) hwy
      apply hne
      rw [← hwp, ← hyq, hyw]
  · rintro ⟨⟨r, hr⟩, hdir, hanti⟩
    letI : PartialOrder P := { (inferInstance : Preorder P) with
      le_antisymm := fun a b h1 h2 => hanti a b h1 h2 }
    have core : ∃ f : BddMorphism (CWorld (Fin 1) (Fin (Fintype.card P))) P,
        Surjective f.toFun := by
      -- a top element
      have htop : ∃ tp : P, ∀ x, x ≤ tp := by
        have h : ∀ s : Finset P, ∃ z : P, ∀ x ∈ s, x ≤ z := by
          intro s
          induction s using Finset.induction_on with
          | empty => exact ⟨r, by simp⟩
          | insert a s ha ih =>
            obtain ⟨z, hz⟩ := ih
            obtain ⟨z', h1, h2⟩ := hdir a z
            refine ⟨z', fun x hx => ?_⟩
            rcases Finset.mem_insert.1 hx with rfl | hx
            · exact h1
            · exact (hz x hx).trans h2
        obtain ⟨z, hz⟩ := h Finset.univ
        exact ⟨z, fun x => hz x (Finset.mem_univ x)⟩
      obtain ⟨tp, htp⟩ := htop
      -- an enumeration of `P` along a linear extension
      obtain ⟨N, hN⟩ : ∃ N, N = Fintype.card P := ⟨_, rfl⟩
      rw [← hN]
      letI : Fintype (LinearExtension P) := inferInstanceAs (Fintype P)
      have hcardL : Fintype.card (LinearExtension P) = N := hN.symm
      let e : Fin N ≃o LinearExtension P := Fintype.orderIsoFinOfCardEq (LinearExtension P) hcardL
      obtain ⟨t, ht⟩ : ∃ t : ℕ → P, ∀ i (h : i < N), t i = e ⟨i, h⟩ :=
        ⟨fun i => if h : i < N then e ⟨i, h⟩ else r, fun i h => by simp [h]⟩
      obtain ⟨pos, hpos⟩ : ∃ pos : P → Fin N, ∀ q, e (pos q) = toLinearExtension q :=
        ⟨fun q => e.symm (toLinearExtension q), fun q => by simp⟩
      have htpos : ∀ q, t (pos q) = q := by
        intro q
        rw [ht _ (pos q).isLt, Fin.eta, hpos]
        rfl
      have hlin : ∀ i j (hi : i < N) (hj : j < N), t i ≤ t j → i ≤ j := by
        intro i j hi hj hle
        have h1 : toLinearExtension (t i) ≤ toLinearExtension (t j) := toLinearExtension.monotone hle
        rw [ht i hi, ht j hj] at h1
        have h2 : e ⟨i, hi⟩ ≤ e ⟨j, hj⟩ := h1
        exact Fin.mk_le_mk.1 (e.le_iff_le.1 h2)
      -- one step of the greedy climb
      have hoff : ∀ (s : ℕ → Bool) i, s i = false → walk t r tp s (i + 1) = walk t r tp s i := by
        intro s i h
        simp only [walk]
        rw [if_neg (by simp [h])]
      have hon1 : ∀ (s : ℕ → Bool) i, s i = true → walk t r tp s i ≤ t i →
          walk t r tp s (i + 1) = t i := by
        intro s i h h'
        simp only [walk]
        rw [if_pos h, if_pos h']
      have hon2 : ∀ (s : ℕ → Bool) i, s i = true → ¬ walk t r tp s i ≤ t i →
          walk t r tp s (i + 1) = tp := by
        intro s i h h'
        simp only [walk]
        rw [if_pos h, if_neg h']
      -- the climb only goes up
      have hmono_time : ∀ (s : ℕ → Bool) i, walk t r tp s i ≤ walk t r tp s (i + 1) := by
        intro s i
        cases hs : s i
        · exact le_of_eq (hoff s i hs).symm
        · by_cases hc : walk t r tp s i ≤ t i
          · rw [hon1 s i hs hc]
            exact hc
          · rw [hon2 s i hs hc]
            exact htp _
      have hmono_time' : ∀ (s : ℕ → Bool) i k, i ≤ k → walk t r tp s i ≤ walk t r tp s k := by
        intro s i k hik
        induction k, hik using Nat.le_induction with
        | base => exact le_rfl
        | succ k _ ih => exact ih.trans (hmono_time s k)
      -- more switches on ⇒ higher
      have hmono_sw : ∀ (s s' : ℕ → Bool), (∀ i, s i = true → s' i = true) →
          ∀ i, walk t r tp s i ≤ walk t r tp s' i := by
        intro s s' hss' i
        induction i with
        | zero => exact le_rfl
        | succ i ih =>
          cases hs' : s' i
          · have hs : s i = false := by
              cases hs : s i
              · rfl
              · have := hss' i hs
                rw [hs'] at this
                exact absurd this (by decide)
            rw [hoff s i hs, hoff s' i hs']
            exact ih
          · by_cases hc : walk t r tp s' i ≤ t i
            · rw [hon1 s' i hs' hc]
              cases hs : s i
              · rw [hoff s i hs]
                exact ih.trans hc
              · rw [hon1 s i hs (ih.trans hc)]
            · rw [hon2 s' i hs' hc]
              exact htp _
      -- reading the switches of a world
      obtain ⟨sw, hsw⟩ : ∃ sw : CWorld (Fin 1) (Fin N) → ℕ → Bool,
          ∀ w i, sw w i = if h : i < N then w.switch ⟨i, h⟩ else false :=
        ⟨fun w i => if h : i < N then w.switch ⟨i, h⟩ else false, fun _ _ => rfl⟩
      -- the back condition
      have hback : ∀ (w : CWorld (Fin 1) (Fin N)) (q : P), walk t r tp (sw w) N ≤ q →
          ∃ y : CWorld (Fin 1) (Fin N), w ≤ y ∧ walk t r tp (sw y) N = q := by
        intro w q hxq
        by_cases hxq' : walk t r tp (sw w) N = q
        · exact ⟨w, le_rfl, hxq'⟩
        obtain ⟨j, hj⟩ : ∃ j, j = (pos q : ℕ) := ⟨_, rfl⟩
        have hjN : j < N := hj ▸ (pos q).isLt
        have htj : t j = q := by rw [hj]; exact htpos q
        let y : CWorld (Fin 1) (Fin N) := ⟨w.clock, fun b => w.switch b || decide ((b : ℕ) = j)⟩
        have hwy : w ≤ y := ⟨le_rfl, fun b hb => by simp [y, hb]⟩
        refine ⟨y, hwy, ?_⟩
        have hswy : ∀ i, sw y i = (sw w i || decide (i = j)) := by
          intro i
          rw [hsw, hsw]
          by_cases hi : i < N
          · simp [hi, y]
          · have : i ≠ j := by omega
            simp [hi, this]
        have hagree : ∀ i, i ≤ j → walk t r tp (sw y) i = walk t r tp (sw w) i := by
          intro i
          induction i with
          | zero => intro _; rfl
          | succ i ih =>
            intro hi
            have hsi : sw y i = sw w i := by
              rw [hswy]
              simp [show i ≠ j by omega]
            simp only [walk]
            rw [hsi, ih (by omega)]
        have hoffafter : ∀ i, j < i → i < N → sw w i = false := by
          intro i hji hiN
          by_contra hne
          have hon : sw w i = true := by simpa using hne
          have hle : walk t r tp (sw w) (i + 1) ≤ walk t r tp (sw w) N :=
            hmono_time' _ _ _ (by omega)
          by_cases hc : walk t r tp (sw w) i ≤ t i
          · rw [hon1 _ _ hon hc] at hle
            have h3 : t i ≤ t j := by
              rw [htj]
              exact hle.trans hxq
            have := hlin i j hiN hjN h3
            omega
          · rw [hon2 _ _ hon hc] at hle
            apply hxq'
            exact le_antisymm hxq (le_trans (htp q) hle)
        have hjstep : walk t r tp (sw y) (j + 1) = q := by
          have hon : sw y j = true := by
            rw [hswy]
            simp
          have hle : walk t r tp (sw y) j ≤ t j := by
            rw [hagree j le_rfl, htj]
            exact (hmono_time' _ _ _ hjN.le).trans hxq
          rw [hon1 _ _ hon hle, htj]
        have hstay : ∀ i, j + 1 ≤ i → i ≤ N → walk t r tp (sw y) i = q := by
          intro i hi1
          induction i, hi1 using Nat.le_induction with
          | base => intro _; exact hjstep
          | succ i hi ih =>
            intro hi2
            have hoff' : sw y i = false := by
              rw [hswy, hoffafter i (by omega) (by omega)]
              simp [show i ≠ j by omega]
            rw [hoff _ _ hoff', ih (by omega)]
        exact hstay N (by omega) le_rfl
      -- the all-off world climbs nowhere
      let w0 : CWorld (Fin 1) (Fin N) := ⟨0, fun _ => false⟩
      have hw0 : ∀ i, walk t r tp (sw w0) i = r := by
        intro i
        induction i with
        | zero => rfl
        | succ i ih =>
          have h0 : sw w0 i = false := by
            rw [hsw]
            split_ifs <;> rfl
          rw [hoff (sw w0) i h0, ih]
      refine ⟨⟨fun w => walk t r tp (sw w) N, ?_, ?_⟩, ?_⟩
      · intro w v hwv
        apply hmono_sw
        intro i hi
        rw [hsw] at hi ⊢
        split_ifs at hi ⊢ with h
        exact hwv.2 _ hi
      · intro w q hq
        exact hback w q hq
      · intro q
        obtain ⟨y, -, hy⟩ := hback w0 q (by rw [hw0]; exact hr q)
        exact ⟨y, hy⟩
    obtain ⟨f, hf⟩ := core
    exact ⟨1, Fintype.card P, f, hf⟩
