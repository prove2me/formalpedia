-- Prove2me | solution 1 for Hirsch.alternating_complement_exchange_routes
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-18T22:09:41.978227+00:00
-- url     : https://prove2.me/submissions/1bc5e00d-3233-4c03-a914-8c8ec6168272

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Hirsch.AlternatingComplement

/-- A complete order-only configuration, retaining either starting parity. -/
def Legal (m : ℕ) {r : ℕ} (h : Fin r → ℕ) : Prop :=
  StrictMono h ∧ (∀ i, h i < m) ∧
    ∃ b : ℕ, b < 2 ∧ ∀ i, h i % 2 = (b + i.val) % 2

def labels {r : ℕ} (h : Fin r → ℕ) : Finset ℕ :=
  Finset.univ.image h

def Good (m r : ℕ) (H : Finset ℕ) : Prop :=
  ∃ h : Fin r → ℕ, Legal m h ∧ labels h = H

def Exchange (r : ℕ) (S T : Finset ℕ) : Prop :=
  S ≠ T ∧ (S ∩ T).card + 1 = r

lemma exchange_symm {r : ℕ} {S T : Finset ℕ} (h : Exchange r S T) :
    Exchange r T S := by
  exact ⟨Ne.symm h.1, by simpa only [Finset.inter_comm] using h.2⟩

private lemma labels_card {r : ℕ} (h : Fin r → ℕ) (hh : StrictMono h) :
    (labels h).card = r := by
  rw [labels, Finset.card_image_of_injective _ hh.injective]
  simp

private lemma labels_subset {m r : ℕ} (h : Fin r → ℕ)
    (hh : ∀ i, h i < m) : labels h ⊆ Finset.range m := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_range.mpr (hh i)

private lemma lower_bound {r : ℕ} (h : Fin r → ℕ) (hh : StrictMono h)
    (b : ℕ) (hb : b < 2) (hp : ∀ i, h i % 2 = (b + i.val) % 2) :
    ∀ i, b + i.val ≤ h i := by
  have aux : ∀ n : ℕ, ∀ hn : n < r, b + n ≤ h ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
      intro hn
      have he := hp ⟨0, hn⟩
      simp only [Fin.val_mk, Nat.add_zero] at he
      omega
    | succ n ih =>
      intro hn
      have hn' : n < r := by omega
      have hlo := ih hn'
      have hidx : (⟨n, hn'⟩ : Fin r) < ⟨n+1, hn⟩ := by
        change n < n+1
        exact Nat.lt_succ_self n
      have hlt : h ⟨n, hn'⟩ < h ⟨n+1, hn⟩ := hh hidx
      omega
  intro i
  exact aux i.val i.isLt

private def packedPrefix {r : ℕ} (b : ℕ) (h : Fin r → ℕ) (t : ℕ) : Fin r → ℕ :=
  fun i => if i.val < t then b + i.val else h i

private lemma prefix_legal {m r : ℕ} (h : Fin r → ℕ)
    (hh : StrictMono h) (hm : ∀ i, h i < m)
    (b : ℕ) (hb : b < 2) (hp : ∀ i, h i % 2 = (b + i.val) % 2) (t : ℕ) :
    Legal m (packedPrefix b h t) := by
  have hlo := lower_bound h hh b hb hp
  refine ⟨?_, ?_, b, hb, ?_⟩
  · intro i j hij
    have hij' : i.val < j.val := hij
    by_cases hi : i.val < t <;> by_cases hj : j.val < t
    · simp only [packedPrefix, if_pos hi, if_pos hj]
      omega
    · simp only [packedPrefix, if_pos hi, if_neg hj]
      have h := hlo j
      omega
    · omega
    · simpa only [packedPrefix, if_neg hi, if_neg hj] using hh hij
  · intro i
    by_cases hi : i.val < t
    · simp only [packedPrefix, if_pos hi]
      exact (hlo i).trans_lt (hm i)
    · simpa only [packedPrefix, if_neg hi] using hm i
  · intro i
    by_cases hi : i.val < t
    · simp only [packedPrefix, if_pos hi]
    · simpa only [packedPrefix, if_neg hi] using hp i

private lemma prefix_zero {r : ℕ} (b : ℕ) (h : Fin r → ℕ) :
    packedPrefix b h 0 = h := by
  funext i
  simp [packedPrefix]

private lemma prefix_full {r : ℕ} (b : ℕ) (h : Fin r → ℕ) :
    packedPrefix b h r = (fun i : Fin r => b + i.val) := by
  funext i
  exact if_pos i.isLt

/-- Changing only one injectively represented label gives equality or one
exchange. No combinatorial edge is assumed. -/
private lemma one_coordinate {r : ℕ} (f g : Fin r → ℕ)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (i : Fin r) (he : ∀ j, j ≠ i → f j = g j) :
    labels f = labels g ∨ Exchange r (labels f) (labels g) := by
  classical
  by_cases heq : labels f = labels g
  · exact Or.inl heq
  right
  have hF : (labels f).card = r := by
    rw [labels, Finset.card_image_of_injective _ hf]
    simp
  have hG : (labels g).card = r := by
    rw [labels, Finset.card_image_of_injective _ hg]
    simp
  let C := (Finset.univ.erase i).image f
  have hC : C.card + 1 = r := by
    dsimp only [C]
    rw [Finset.card_image_of_injective _ hf]
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_erase_add_one (Finset.mem_univ i)
  have hsub : C ⊆ labels f ∩ labels g := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    refine Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, (he j hji).symm⟩
  have hlow := Finset.card_le_card hsub
  have hlt : (labels f ∩ labels g).card < r := by
    by_contra hn
    have hI : labels f ∩ labels g = labels f :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hFG : labels f ⊆ labels g := Finset.inter_eq_left.mp hI
    exact heq (Finset.eq_of_subset_of_card_le hFG (by omega))
  exact ⟨heq, by omega⟩

private lemma prefix_step {m r : ℕ} (h : Fin r → ℕ)
    (hh : StrictMono h) (hm : ∀ i, h i < m)
    (b : ℕ) (hb : b < 2) (hp : ∀ i, h i % 2 = (b + i.val) % 2)
    (t : ℕ) (ht : t < r) :
    labels (packedPrefix b h t) = labels (packedPrefix b h (t+1)) ∨
      Exchange r (labels (packedPrefix b h t)) (labels (packedPrefix b h (t+1))) := by
  apply one_coordinate _ _
    (prefix_legal h hh hm b hb hp t).1.injective
    (prefix_legal h hh hm b hb hp (t+1)).1.injective ⟨t, ht⟩
  intro j hj
  have hne : j.val ≠ t := by
    intro he
    apply hj
    exact Fin.ext he
  have he : (j.val < t) ↔ (j.val < t+1) := by omega
  simp only [packedPrefix, he]

/-- The two packed phases differ by one boundary label, not r coordinate
moves. The r=0 case is an equality and will be removed. -/
private lemma anchor_step (r b c : ℕ) (hb : b < 2) (hc : c < 2) :
    labels (fun i : Fin r => b + i.val) = labels (fun i : Fin r => c + i.val) ∨
      Exchange r (labels (fun i : Fin r => b + i.val))
        (labels (fun i : Fin r => c + i.val)) := by
  classical
  have h01 : labels (fun i : Fin r => 0 + i.val) = labels (fun i : Fin r => 1 + i.val) ∨
      Exchange r (labels (fun i : Fin r => 0 + i.val))
        (labels (fun i : Fin r => 1 + i.val)) := by
    by_cases hr : r = 0
    · subst r
      left
      simp [labels]
    · have hr0 : 0 < r := by omega
      let f : Fin r → ℕ := fun i => i.val
      let g : Fin r → ℕ := fun i => if i.val = 0 then r else i.val
      have hf : Function.Injective f := by
        intro i j he
        exact Fin.ext he
      have hg : Function.Injective g := by
        intro i j he
        by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
        · exact Fin.ext (hi.trans hj.symm)
        · simp only [g, if_pos hi, if_neg hj] at he
          have hh := j.isLt
          omega
        · simp only [g, if_neg hi, if_pos hj] at he
          have hh := i.isLt
          omega
        · apply Fin.ext
          simpa only [g, if_neg hi, if_neg hj] using he
      have hother : ∀ j : Fin r, j ≠ ⟨0, hr0⟩ → f j = g j := by
        intro j hj
        have hn : j.val ≠ 0 := by intro he; exact hj (Fin.ext he)
        simp [f, g, hn]
      have heq : labels g = labels (fun i : Fin r => 1 + i.val) := by
        ext x
        constructor
        · intro hx
          obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
          have hx0 : 0 < x ∧ x ≤ r := by
            by_cases hz : i.val = 0
            · simp only [g, if_pos hz] at hi
              omega
            · simp only [g, if_neg hz] at hi
              have hh := i.isLt
              omega
          exact Finset.mem_image.mpr ⟨⟨x-1, by omega⟩, Finset.mem_univ _, by change 1+(x-1) = x; omega⟩
        · intro hx
          obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
          have hh := i.isLt
          have hx0 : 0 < x ∧ x ≤ r := by
            have hi' : 1+i.val = x := hi
            omega
          by_cases hxr : x = r
          · exact Finset.mem_image.mpr ⟨⟨0, hr0⟩, Finset.mem_univ _, by simp [g, hxr]⟩
          · have hxm : x < r := by omega
            exact Finset.mem_image.mpr ⟨⟨x, hxm⟩, Finset.mem_univ _, by simp [g, ne_of_gt hx0.1]⟩
      have h := one_coordinate f g hf hg ⟨0, hr0⟩ hother
      rw [heq] at h
      simpa only [f, Nat.zero_add] using h
  have hb' : b = 0 ∨ b = 1 := by omega
  have hc' : c = 0 ∨ c = 1 := by omega
  rcases hb' with rfl | rfl <;> rcases hc' with rfl | rfl
  · exact Or.inl rfl
  · exact h01
  · rcases h01 with h | h
    · exact Or.inl h.symm
    · exact Or.inr (exchange_symm h)
  · exact Or.inl rfl

/-- Delete stationary transitions from an explicitly supplied finite schedule.
This helper proves compression; the schedule itself is constructed below. -/
private lemma compress_schedule {E : Type*} (valid : E → Prop) (edge : E → E → Prop)
    (N : ℕ) (a : ℕ → E)
    (hv : ∀ i, i ≤ N → valid (a i))
    (he : ∀ i, i < N → a i = a (i+1) ∨ edge (a i) (a (i+1))) :
    ∃ L : ℕ, L ≤ N ∧ ∃ p : ℕ → E,
      p 0 = a 0 ∧ p L = a N ∧ (∀ i, i ≤ L → valid (p i)) ∧
      ∀ i, i < L → edge (p i) (p (i+1)) := by
  induction N generalizing a with
  | zero =>
    refine ⟨0, le_rfl, a, rfl, rfl, hv, ?_⟩
    intro i hi
    omega
  | succ N ih =>
    obtain ⟨L, hL, p, hp0, hpL, hpv, hpe⟩ := ih (fun i => a (i+1))
      (fun i hi => hv (i+1) (by omega)) (fun i hi => he (i+1) (by omega))
    rcases he 0 (by omega) with h | h
    · refine ⟨L, by omega, p, hp0.trans h.symm, hpL, hpv, hpe⟩
    · let q : ℕ → E := fun i => match i with
        | 0 => a 0
        | j+1 => p j
      refine ⟨L+1, by omega, q, rfl, hpL, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero => exact hv 0 (by omega)
        | succ i => exact hpv i (by omega)
      · intro i hi
        cases i with
        | zero => simpa only [q, hp0] using h
        | succ i => exact hpe i (by omega)

/-- Left-pack each phase, cross once between the anchors, and reverse the
other packing. The actual schedule uses at most 2r+1 nontrivial exchanges. -/
theorem route {m r : ℕ} (h k : Fin r → ℕ) (hh : Legal m h) (hk : Legal m k) :
    ∃ L : ℕ, L ≤ 2*r+1 ∧ ∃ p : ℕ → Finset ℕ,
      p 0 = labels h ∧ p L = labels k ∧
      (∀ i, i ≤ L → Good m r (p i)) ∧
      ∀ i, i < L → Exchange r (p i) (p (i+1)) := by
  classical
  obtain ⟨hh, hhm, b, hb, hhp⟩ := hh
  obtain ⟨hk, hkm, c, hc, hkp⟩ := hk
  let A : ℕ → Finset ℕ := fun t =>
    if t ≤ r then labels (packedPrefix b h t) else labels (packedPrefix c k (2*r+1-t))
  have hgood : ∀ t, Good m r (A t) := by
    intro t
    dsimp only [A]
    split_ifs
    · exact ⟨_, prefix_legal h hh hhm b hb hhp t, rfl⟩
    · exact ⟨_, prefix_legal k hk hkm c hc hkp (2*r+1-t), rfl⟩
  have hstep : ∀ t, t < 2*r+1 → A t = A (t+1) ∨ Exchange r (A t) (A (t+1)) := by
    intro t ht
    rcases lt_trichotomy t r with htr | htr | htr
    · have h0 : t ≤ r := by omega
      have h1 : t+1 ≤ r := by omega
      simpa only [A, if_pos h0, if_pos h1] using prefix_step h hh hhm b hb hhp t htr
    · subst t
      have h0 : ¬ (r+1 ≤ r) := by omega
      have hn : 2*r+1-(r+1) = r := by omega
      simpa only [A, if_pos (le_refl r), if_neg h0, hn, prefix_full] using anchor_step r b c hb hc
    · have h0 : ¬ (t ≤ r) := by omega
      have h1 : ¬ (t+1 ≤ r) := by omega
      let s := 2*r-t
      have hs : s < r := by dsimp only [s]; omega
      have he0 : 2*r+1-t = s+1 := by dsimp only [s]; omega
      have he1 : 2*r+1-(t+1) = s := by dsimp only [s]; omega
      have h := prefix_step k hk hkm c hc hkp s hs
      have hr : labels (packedPrefix c k (s+1)) = labels (packedPrefix c k s) ∨
          Exchange r (labels (packedPrefix c k (s+1))) (labels (packedPrefix c k s)) := by
        rcases h with h | h
        · exact Or.inl h.symm
        · exact Or.inr (exchange_symm h)
      simpa only [A, if_neg h0, if_neg h1, he0, he1] using hr
  obtain ⟨L, hL, p, hp0, hpL, hpv, hpe⟩ :=
    compress_schedule (Good m r) (Exchange r) (2*r+1) A (fun i _ => hgood i) hstep
  have hA0 : A 0 = labels h := by simp [A, prefix_zero]
  have hAN : A (2*r+1) = labels k := by
    have hn : ¬ (2*r+1 ≤ r) := by omega
    simp only [A, if_neg hn, Nat.sub_self, prefix_zero]
  exact ⟨L, hL, p, hp0.trans hA0, hpL.trans hAN, hpv, hpe⟩

/-- Complementing an exchange gives an exchange of selected original labels,
with the correct complementary cardinality. -/
private lemma complement_exchange {m r : ℕ} {S T : Finset ℕ}
    (hS : S ⊆ Finset.range m) (hT : T ⊆ Finset.range m)
    (hcS : S.card = r) (hcT : T.card = r) (he : Exchange r S T) :
    Exchange (m-r) (Finset.range m \ S) (Finset.range m \ T) := by
  classical
  have hU : S ∪ T ⊆ Finset.range m := Finset.union_subset hS hT
  have huc := Finset.card_union_add_card_inter S T
  have hUc : (S ∪ T).card = r+1 := by have hh := he.2; omega
  have hbound := Finset.card_le_card hU
  simp only [Finset.card_range, hUc] at hbound
  have hI : (Finset.range m \ S) ∩ (Finset.range m \ T) =
      Finset.range m \ (S ∪ T) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union]
    tauto
  refine ⟨?_, ?_⟩
  · intro hh
    apply he.1
    ext x
    by_cases hx : x ∈ Finset.range m
    · have hx' := congrArg (fun U : Finset ℕ => x ∈ U) hh
      simp only [Finset.mem_sdiff, hx, true_and] at hx'
      tauto
    · have hs : x ∉ S := fun hs => hx (hS hs)
      have ht : x ∉ T := fun ht => hx (hT ht)
      simp [hs, ht]
  · rw [hI, Finset.card_sdiff_of_subset hU, Finset.card_range, hUc]
    omega

end Hirsch.AlternatingComplement

/-- Uniform single-label exchange routes for both alternating complement
phases. All intermediate configurations are constructed; no path is a premise. -/
theorem solution (m r : ℕ) (h k : Fin r → ℕ)
    (hh : StrictMono h) (hk : StrictMono k)
    (hhm : ∀ i, h i < m) (hkm : ∀ i, k i < m)
    (hphase : ∃ b : ℕ, b < 2 ∧ ∀ i, h i % 2 = (b + i.val) % 2)
    (kphase : ∃ b : ℕ, b < 2 ∧ ∀ i, k i % 2 = (b + i.val) % 2) :
    ∃ L : ℕ, L ≤ 2*r+1 ∧ ∃ p : ℕ → Finset ℕ,
      p 0 = Finset.univ.image h ∧ p L = Finset.univ.image k ∧
      (∀ t, t ≤ L → p t ⊆ Finset.range m ∧ (p t).card = r ∧
        (Finset.range m \ p t).card = m-r ∧
        ∃ a : Fin r → ℕ, StrictMono a ∧ (∀ i, a i < m) ∧
          (∃ b : ℕ, b < 2 ∧ ∀ i, a i % 2 = (b + i.val) % 2) ∧
          Finset.univ.image a = p t) ∧
      (∀ t, t < L → p t ≠ p (t+1) ∧ (p t ∩ p (t+1)).card + 1 = r ∧
        (Finset.range m \ p t) ≠ (Finset.range m \ p (t+1)) ∧
        ((Finset.range m \ p t) ∩ (Finset.range m \ p (t+1))).card + 1 = m-r) := by
  classical
  obtain ⟨L, hL, p, hp0, hpL, hpv, hpe⟩ :=
    Hirsch.AlternatingComplement.route h k ⟨hh, hhm, hphase⟩ ⟨hk, hkm, kphase⟩
  have hv : ∀ t, t ≤ L → p t ⊆ Finset.range m ∧ (p t).card = r := by
    intro t ht
    obtain ⟨a, ha, he⟩ := hpv t ht
    rw [← he]
    exact ⟨Hirsch.AlternatingComplement.labels_subset a ha.2.1,
      Hirsch.AlternatingComplement.labels_card a ha.1⟩
  refine ⟨L, hL, p, hp0, hpL, ?_, ?_⟩
  · intro t ht
    obtain ⟨a, ha, he⟩ := hpv t ht
    have hc : (Finset.range m \ p t).card = m-r := by
      rw [Finset.card_sdiff_of_subset (hv t ht).1, Finset.card_range, (hv t ht).2]
    exact ⟨(hv t ht).1, (hv t ht).2, hc, a, ha.1, ha.2.1, ha.2.2, he⟩
  · intro t ht
    have hs := hv t (by omega)
    have hu := hv (t+1) (by omega)
    have he := hpe t ht
    have hc := Hirsch.AlternatingComplement.complement_exchange hs.1 hu.1 hs.2 hu.2 he
    exact ⟨he.1, he.2, hc.1, hc.2⟩

#print axioms Hirsch.AlternatingComplement.lower_bound
#print axioms Hirsch.AlternatingComplement.one_coordinate
#print axioms Hirsch.AlternatingComplement.anchor_step
#print axioms Hirsch.AlternatingComplement.route
#print axioms solution
