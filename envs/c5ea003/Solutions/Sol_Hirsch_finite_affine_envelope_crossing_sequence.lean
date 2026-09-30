-- Prove2me | solution 1 for Hirsch.finite_affine_envelope_crossing_sequence
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-14T04:01:17.417332+00:00
-- url     : https://prove2.me/submissions/cf94f560-6133-4340-867d-36624f0e82db

import Mathlib

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Hirsch.FiniteAffineChambers

/-- A strict sign change of an affine scalar has an interior zero. -/
lemma zero_of_sign_change (a b l r : ℝ) (hlr : l < r)
    (hl : a + l*b < 0) (hr : 0 < a + r*b) :
    ∃ t : ℝ, l < t ∧ t < r ∧ a + t*b = 0 := by
  have hb : 0 < b := by
    by_contra hn
    have hp := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlr.le)
      (le_of_not_gt hn)
    nlinarith
  refine ⟨-a/b, (lt_div_iff₀ hb).mpr (by linarith),
    (div_lt_iff₀ hb).mpr (by linarith), ?_⟩
  rw [div_mul_cancel₀ _ (ne_of_gt hb)]
  ring

/-- A negative value and absence of interior zeros give strict negativity on
an entire chamber and the correct weak inequalities at BOTH boundary points. -/
lemma chamber_sign (a b l r s : ℝ) (hls : l < s) (hsr : s < r)
    (hs : a + s*b < 0)
    (hzero : ∀ t : ℝ, l < t → t < r → a + t*b ≠ 0) :
    (∀ t : ℝ, l ≤ t → t ≤ r → a + t*b ≤ 0) ∧
    (∀ t : ℝ, l < t → t < r → a + t*b < 0) := by
  have hclosed : ∀ t : ℝ, l ≤ t → t ≤ r → a + t*b ≤ 0 := by
    intro t hlt htr
    by_contra hn
    have ht : 0 < a + t*b := lt_of_not_ge hn
    rcases lt_trichotomy s t with hst | he | hts
    · obtain ⟨u, hsu, hut, hu⟩ := zero_of_sign_change a b s t hst hs ht
      exact hzero u (hls.trans hsu) (hut.trans_le htr) hu
    · subst t
      linarith
    · obtain ⟨u, htu, hus, hu⟩ := zero_of_sign_change (-a) (-b) t s hts
        (by nlinarith) (by nlinarith)
      exact hzero u (hlt.trans_lt htu) (hus.trans hsr) (by nlinarith [hu])
  exact ⟨hclosed, fun t hlt htr =>
    lt_of_le_of_ne (hclosed t hlt.le htr.le) (hzero t hlt htr)⟩

/-- Construct a finite ordered chamber decomposition from the ACTUAL affine
scores. No root list, interval winners, or wall-maximizing oracle is supplied.
Injectivity at time zero rules out identical affine scores within a factor.
Unused comparisons may create stationary adjacent chambers. -/
theorem exists_chambers
    (m : ℕ) (k : Fin m → ℕ)
    (a b : (i : Fin m) → Fin (k i) → ℝ)
    (p0 p1 : (i : Fin m) → Fin (k i))
    (ha : ∀ i, Function.Injective (a i))
    (hp0 : ∀ i q, q ≠ p0 i → a i q < a i (p0 i))
    (hp1 : ∀ i q, q ≠ p1 i → a i q + b i q < a i (p1 i) + b i (p1 i)) :
    ∃ (N : ℕ) (cut : Fin (N+2) → ℝ)
      (pick : Fin (N+1) → (i : Fin m) → Fin (k i)),
      StrictMono cut ∧ cut 0 = 0 ∧ cut (Fin.last (N+1)) = 1 ∧
      pick 0 = p0 ∧ pick (Fin.last N) = p1 ∧
      (∀ j i q, q ≠ pick j i → ∀ t : ℝ,
        cut j.castSucc < t → t < cut j.succ →
        a i q + t*b i q < a i (pick j i) + t*b i (pick j i)) ∧
      (∀ j i q, ∀ t : ℝ,
        cut j.castSucc ≤ t → t ≤ cut j.succ →
        a i q + t*b i q ≤ a i (pick j i) + t*b i (pick j i)) := by
  classical
  let roots : Finset ℝ := (Finset.univ : Finset (Fin m)).biUnion fun i =>
    (Finset.univ : Finset (Fin (k i))).biUnion fun p =>
      (Finset.univ : Finset (Fin (k i))).image fun q =>
        (a i q-a i p)/(b i p-b i q)
  let C : Finset ℝ := insert 0 (insert 1 (roots.filter (fun t => 0 < t ∧ t < 1)))
  have h0 : (0 : ℝ) ∈ C := by simp [C]
  have h1 : (1 : ℝ) ∈ C := by simp [C]
  have hC : ∀ t ∈ C, 0 ≤ t ∧ t ≤ 1 := by
    intro t ht
    simp only [C, Finset.mem_insert, Finset.mem_filter] at ht
    rcases ht with rfl | rfl | ⟨_, hl, hr⟩
    · norm_num
    · norm_num
    · exact ⟨hl.le, hr.le⟩
  have hcard : 2 ≤ C.card := by
    have hs : ({0, 1} : Finset ℝ) ⊆ C := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact h0
      · exact h1
    have hh := Finset.card_le_card hs
    norm_num at hh
    exact hh
  let N := C.card-2
  have hc : C.card = N+2 := by dsimp [N]; omega
  let cut : Fin (N+2) ↪o ℝ := C.orderEmbOfFin hc
  have hmem : ∀ j, cut j ∈ C := fun j => C.orderEmbOfFin_mem hc j
  have honto : ∀ t ∈ C, ∃ j, cut j = t := by
    intro t ht
    refine ⟨(C.orderIsoOfFin hc).symm ⟨t, ht⟩, ?_⟩
    exact congrArg Subtype.val ((C.orderIsoOfFin hc).apply_symm_apply ⟨t, ht⟩)
  have hz : cut 0 = 0 := by
    obtain ⟨j, hj⟩ := honto 0 h0
    have hh := cut.monotone (Fin.zero_le j)
    rw [hj] at hh
    exact le_antisymm hh (hC _ (hmem 0)).1
  have ho : cut (Fin.last (N+1)) = 1 := by
    obtain ⟨j, hj⟩ := honto 1 h1
    have hh := cut.monotone (Fin.le_last j)
    rw [hj] at hh
    exact le_antisymm (hC _ (hmem _)).2 hh
  have hgap : ∀ (j : Fin (N+1)) (t : ℝ),
      cut j.castSucc < t → t < cut j.succ → t ∉ C := by
    intro j t hl hr ht
    obtain ⟨v, hv⟩ := honto t ht
    have hlv : j.castSucc < v := cut.lt_iff_lt.mp (by simpa [hv] using hl)
    have hvr : v < j.succ := cut.lt_iff_lt.mp (by simpa [hv] using hr)
    have hv1 : j.val < v.val := hlv
    have hv2 : v.val < j.val+1 := hvr
    omega
  have htie : ∀ i p q, p ≠ q → ∀ t : ℝ, 0 < t → t < 1 →
      a i p+t*b i p = a i q+t*b i q → t ∈ C := by
    intro i p q hpq t ht0 ht1 he
    have hd : b i p-b i q ≠ 0 := by
      intro hh
      have hh' := sub_eq_zero.mp hh
      have haa : a i p = a i q := by nlinarith [he]
      exact hpq (ha i haa)
    have heq : (a i q-a i p)/(b i p-b i q) = t := by
      apply (div_eq_iff hd).mpr
      nlinarith [he]
    have hr : t ∈ roots := by
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ _, Finset.mem_biUnion.mpr ?_⟩
      exact ⟨p, Finset.mem_univ _, Finset.mem_image.mpr ⟨q, Finset.mem_univ _, heq⟩⟩
    simp only [C, Finset.mem_insert, Finset.mem_filter]
    exact Or.inr (Or.inr ⟨hr, ht0, ht1⟩)
  let sample : Fin (N+1) → ℝ := fun j => (cut j.castSucc+cut j.succ)/2
  have hs : ∀ j : Fin (N+1), cut j.castSucc < sample j ∧ sample j < cut j.succ := by
    intro j
    have hh : cut j.castSucc < cut j.succ := cut.strictMono (by
      show j.val < j.val+1
      omega)
    dsimp [sample]
    constructor <;> linarith
  have hpick : ∀ (j : Fin (N+1)) (i : Fin m), ∃ p : Fin (k i),
      ∀ q : Fin (k i), a i q+sample j*b i q ≤ a i p+sample j*b i p := by
    intro j i
    obtain ⟨p, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (k i)))
      (fun q => a i q+sample j*b i q) ⟨p0 i, Finset.mem_univ _⟩
    exact ⟨p, fun q => hmax q (Finset.mem_univ _)⟩
  choose pick hmax using hpick
  have hsample : ∀ j i q, q ≠ pick j i →
      a i q+sample j*b i q < a i (pick j i)+sample j*b i (pick j i) := by
    intro j i q hq
    apply lt_of_le_of_ne (hmax j i q)
    intro he
    exact hgap j (sample j) (hs j).1 (hs j).2
      (htie i q (pick j i) hq (sample j)
        ((hC _ (hmem _)).1.trans_lt (hs j).1)
        ((hs j).2.trans_le (hC _ (hmem _)).2) he)
  have hsign : ∀ j i q, q ≠ pick j i →
      (∀ t : ℝ, cut j.castSucc ≤ t → t ≤ cut j.succ →
        a i q+t*b i q ≤ a i (pick j i)+t*b i (pick j i)) ∧
      (∀ t : ℝ, cut j.castSucc < t → t < cut j.succ →
        a i q+t*b i q < a i (pick j i)+t*b i (pick j i)) := by
    intro j i q hq
    have hn : ∀ t : ℝ, cut j.castSucc < t → t < cut j.succ →
        (a i q-a i (pick j i))+t*(b i q-b i (pick j i)) ≠ 0 := by
      intro t hl hr he
      apply hgap j t hl hr
      apply htie i q (pick j i) hq t
        ((hC _ (hmem _)).1.trans_lt hl) (hr.trans_le (hC _ (hmem _)).2)
      nlinarith [he]
    obtain ⟨hw, ht⟩ := chamber_sign (a i q-a i (pick j i))
      (b i q-b i (pick j i)) (cut j.castSucc) (cut j.succ) (sample j)
      (hs j).1 (hs j).2 (by have hh := hsample j i q hq; nlinarith) hn
    constructor
    · intro t hl hr
      have hh := hw t hl hr
      nlinarith
    · intro t hl hr
      have hh := ht t hl hr
      nlinarith
  have hweak : ∀ j i q, ∀ t : ℝ, cut j.castSucc ≤ t → t ≤ cut j.succ →
      a i q+t*b i q ≤ a i (pick j i)+t*b i (pick j i) := by
    intro j i q t hl hr
    by_cases he : q = pick j i
    · subst q
      exact le_rfl
    · exact (hsign j i q he).1 t hl hr
  have hfirst : pick 0 = p0 := by
    funext i
    by_contra he
    have hu := hp0 i (pick 0 i) he
    have hw := hweak 0 i (p0 i) 0 (by simpa using hz.le) (hC _ (hmem _)).1
    simp only [zero_mul, add_zero] at hw
    linarith
  have hlast : pick (Fin.last N) = p1 := by
    funext i
    by_contra he
    have hu := hp1 i (pick (Fin.last N) i) he
    have hw := hweak (Fin.last N) i (p1 i) 1 (hC _ (hmem _)).2
      (by simpa using ho.ge)
    simp only [one_mul] at hw
    linarith
  exact ⟨N, cut, pick, cut.strictMono, hz, ho, hfirst, hlast,
    fun j i q hq => (hsign j i q hq).2, hweak⟩

#print axioms zero_of_sign_change
#print axioms chamber_sign
#print axioms exists_chambers
end Hirsch.FiniteAffineChambers

namespace Hirsch.FiniteAffineChambers

/-- Delete stationary states while retaining the increasing sample order,
pointwise properties, and every genuine transition relation. The ending sample
may move earlier; its state remains the requested endpoint. -/
lemma compress_sequence {α : Type*} (P : ℝ → α → Prop) (R : α → α → Prop)
    (n : ℕ) (x : ℕ → α) (t : ℕ → ℝ)
    (ht : ∀ j, j < n → t j < t (j+1))
    (hP : ∀ j, j ≤ n → P (t j) (x j))
    (hR : ∀ j, j < n → R (x j) (x (j+1))) :
    ∃ (l : ℕ) (y : ℕ → α) (s : ℕ → ℝ),
      l ≤ n ∧ y 0 = x 0 ∧ y l = x n ∧
      (∀ j, j < l → s j < s (j+1)) ∧
      (∀ j, j ≤ l → P (s j) (y j)) ∧
      (∀ j, j < l → R (y j) (y (j+1))) ∧
      (∀ j, j < l → y j ≠ y (j+1)) ∧
      (∀ j, j ≤ l → s j ≤ t n) := by
  classical
  induction n with
  | zero =>
    refine ⟨0, x, t, le_rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj; omega
    · intro j hj
      have he : j = 0 := by omega
      subst j
      exact hP 0 le_rfl
    · intro j hj; omega
    · intro j hj; omega
    · intro j hj
      have he : j = 0 := by omega
      subst j
      exact le_rfl
  | succ n ih =>
    obtain ⟨l, y, s, hln, hy0, hyn, hs, hyP, hyR, hyne, hst⟩ :=
      ih (fun j hj => ht j (by omega))
        (fun j hj => hP j (by omega)) (fun j hj => hR j (by omega))
    have htn : t n < t (n+1) := ht n (by omega)
    by_cases he : x n = x (n+1)
    · refine ⟨l, y, s, by omega, hy0, hyn.trans he, hs, hyP, hyR, hyne, ?_⟩
      intro j hj
      exact (hst j hj).trans htn.le
    · let z : ℕ → α := fun j => if j ≤ l then y j else x (n+1)
      let u : ℕ → ℝ := fun j => if j ≤ l then s j else t (n+1)
      refine ⟨l+1, z, u, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [z] using hy0
      · simp [z]
      · intro j hj
        by_cases hjl : j < l
        · have hj0 : j ≤ l := by omega
          have hj1 : j+1 ≤ l := by omega
          simpa [u, hj0, hj1] using hs j hjl
        · have hjl' : j = l := by omega
          subst j
          simpa [u] using (hst l le_rfl).trans_lt htn
      · intro j hj
        by_cases hjl : j ≤ l
        · simpa [u, z, hjl] using hyP j hjl
        · simpa [u, z, hjl] using hP (n+1) le_rfl
      · intro j hj
        by_cases hjl : j < l
        · have hj0 : j ≤ l := by omega
          have hj1 : j+1 ≤ l := by omega
          simpa [z, hj0, hj1] using hyR j hjl
        · have hjl' : j = l := by omega
          subst j
          simpa [z, hyn] using hR n (by omega)
      · intro j hj
        by_cases hjl : j < l
        · have hj0 : j ≤ l := by omega
          have hj1 : j+1 ≤ l := by omega
          simpa [z, hj0, hj1] using hyne j hjl
        · have hjl' : j = l := by omega
          subst j
          simpa [z, hyn] using he
      · intro j hj
        by_cases hjl : j ≤ l
        · simpa [u, hjl] using (hst j hjl).trans htn.le
        · simp [u, hjl]

/-- The finite crossing itinerary is derived, including stationary compression.
Every retained sample has a unique winner. Neighboring winners have a common
wall at which BOTH are globally maximizing in every factor. -/
theorem exists_itinerary
    (m : ℕ) (k : Fin m → ℕ)
    (a b : (i : Fin m) → Fin (k i) → ℝ)
    (p0 p1 : (i : Fin m) → Fin (k i))
    (ha : ∀ i, Function.Injective (a i))
    (hp0 : ∀ i q, q ≠ p0 i → a i q < a i (p0 i))
    (hp1 : ∀ i q, q ≠ p1 i → a i q + b i q < a i (p1 i) + b i (p1 i)) :
    ∃ (N : ℕ) (time : ℕ → ℝ)
      (pick : ℕ → (i : Fin m) → Fin (k i)),
      pick 0 = p0 ∧ pick N = p1 ∧
      (∀ j, j < N → time j < time (j+1)) ∧
      (∀ j, j ≤ N → 0 < time j ∧ time j < 1 ∧
        ∀ i q, q ≠ pick j i →
          a i q+time j*b i q < a i (pick j i)+time j*b i (pick j i)) ∧
      (∀ j, j < N → pick j ≠ pick (j+1)) ∧
      (∀ j, j < N → ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧
        (∀ i q, a i q+u*b i q ≤ a i (pick j i)+u*b i (pick j i)) ∧
        (∀ i, a i (pick (j+1) i)+u*b i (pick (j+1) i) =
          a i (pick j i)+u*b i (pick j i))) := by
  classical
  obtain ⟨n, cut, p, hc, hz, ho, hpz, hpo, hstrict, hweak⟩ :=
    exists_chambers m k a b p0 p1 ha hp0 hp1
  let mid : Fin (n+1) → ℝ := fun j => (cut j.castSucc+cut j.succ)/2
  have hmid : ∀ j : Fin (n+1), cut j.castSucc < mid j ∧ mid j < cut j.succ := by
    intro j
    have hh := hc (show j.castSucc < j.succ by show j.val < j.val+1; omega)
    dsimp [mid]
    constructor <;> linarith
  have hcut : ∀ j, 0 ≤ cut j ∧ cut j ≤ 1 := by
    intro j
    constructor
    · have hh := hc.monotone (Fin.zero_le j); simpa [hz] using hh
    · have hh := hc.monotone (Fin.le_last j); simpa [ho] using hh
  let x : ℕ → (i : Fin m) → Fin (k i) := fun j =>
    if hj : j < n+1 then p ⟨j, hj⟩ else p1
  let t : ℕ → ℝ := fun j => if hj : j < n+1 then mid ⟨j, hj⟩ else 1
  let P : ℝ → ((i : Fin m) → Fin (k i)) → Prop := fun s v =>
    0 < s ∧ s < 1 ∧ ∀ i q, q ≠ v i → a i q+s*b i q < a i (v i)+s*b i (v i)
  let R : ((i : Fin m) → Fin (k i)) → ((i : Fin m) → Fin (k i)) → Prop :=
    fun v w => ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧
      (∀ i q, a i q+u*b i q ≤ a i (v i)+u*b i (v i)) ∧
      (∀ i, a i (w i)+u*b i (w i) = a i (v i)+u*b i (v i))
  have ht : ∀ j, j < n → t j < t (j+1) := by
    intro j hj
    have hj0 : j < n+1 := by omega
    have hj1 : j+1 < n+1 := by omega
    have hleft := (hmid ⟨j, hj0⟩).2
    have hright := (hmid ⟨j+1, hj1⟩).1
    have he : (⟨j, hj0⟩ : Fin (n+1)).succ = (⟨j+1, hj1⟩ : Fin (n+1)).castSucc := by
      apply Fin.ext
      rfl
    rw [he] at hleft
    simpa only [t, dif_pos hj0, dif_pos hj1] using hleft.trans hright
  have hP : ∀ j, j ≤ n → P (t j) (x j) := by
    intro j hj
    have hj0 : j < n+1 := by omega
    have hm := hmid ⟨j, hj0⟩
    have h0 := (hcut (⟨j, hj0⟩ : Fin (n+1)).castSucc).1.trans_lt hm.1
    have h1 := hm.2.trans_le (hcut (⟨j, hj0⟩ : Fin (n+1)).succ).2
    have hh : P (mid ⟨j, hj0⟩) (p ⟨j, hj0⟩) :=
      ⟨h0, h1, fun i q hq => hstrict ⟨j, hj0⟩ i q hq _ hm.1 hm.2⟩
    simpa only [t, x, dif_pos hj0] using hh
  have hR : ∀ j, j < n → R (x j) (x (j+1)) := by
    intro j hj
    have hj0 : j < n+1 := by omega
    have hj1 : j+1 < n+1 := by omega
    let l : Fin (n+1) := ⟨j, hj0⟩
    let r : Fin (n+1) := ⟨j+1, hj1⟩
    have he : l.succ = r.castSucc := by apply Fin.ext; rfl
    have hlr : cut l.castSucc ≤ cut l.succ := hc.monotone (by show j ≤ j+1; omega)
    have hrr : cut r.castSucc ≤ cut r.succ := hc.monotone (by show j+1 ≤ j+1+1; omega)
    have hleft : ∀ i q, a i q+cut l.succ*b i q ≤
        a i (p l i)+cut l.succ*b i (p l i) :=
      fun i q => hweak l i q _ hlr le_rfl
    have hright : ∀ i q, a i q+cut l.succ*b i q ≤
        a i (p r i)+cut l.succ*b i (p r i) := by
      intro i q
      rw [he]
      exact hweak r i q _ le_rfl hrr
    have hh : R (p l) (p r) := by
      refine ⟨cut l.succ, (hcut _).1, (hcut _).2, hleft, ?_⟩
      intro i
      exact le_antisymm (hleft i (p r i)) (hright i (p l i))
    simpa only [R, x, dif_pos hj0, dif_pos hj1, l, r] using hh
  obtain ⟨N, y, s, _, hy0, hyn, hs, hyP, hyR, hyne, _⟩ :=
    compress_sequence P R n x t ht hP hR
  have hx0 : x 0 = p0 := by simpa [x] using hpz
  have hxn : x n = p1 := by simpa [x] using hpo
  exact ⟨N, s, y, hy0.trans hx0, hyn.trans hxn, hs, hyP, hyne, hyR⟩

#print axioms compress_sequence
#print axioms exists_itinerary
end Hirsch.FiniteAffineChambers

namespace Hirsch.FiniteAffineChambers

lemma root_between (a b s t u : ℝ) (hst : s < t)
    (hs : a+s*b < 0) (ht : 0 < a+t*b) (hu : a+u*b = 0) : s < u ∧ u < t := by
  obtain ⟨v, hsv, hvt, hv⟩ := zero_of_sign_change a b s t hst hs ht
  have hb : b ≠ 0 := by intro hb; simp [hb] at hs ht; linarith
  have he : (u-v)*b = 0 := by nlinarith [hu, hv]
  have huv : u = v := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hb)
  simpa [huv] using (show s < v ∧ v < t from ⟨hsv, hvt⟩)

/-- Chronological retained crossings: no stationary step remains, and each
common supporting wall lies strictly between its two retained samples. -/
theorem crossing_sequence
    (m : ℕ) (k : Fin m → ℕ)
    (a b : (i : Fin m) → Fin (k i) → ℝ)
    (p0 p1 : (i : Fin m) → Fin (k i))
    (ha : ∀ i, Function.Injective (a i))
    (hp0 : ∀ i q, q ≠ p0 i → a i q < a i (p0 i))
    (hp1 : ∀ i q, q ≠ p1 i → a i q + b i q < a i (p1 i) + b i (p1 i)) :
    ∃ (N : ℕ) (time : ℕ → ℝ)
      (pick : ℕ → (i : Fin m) → Fin (k i)),
      pick 0 = p0 ∧ pick N = p1 ∧
      (∀ j, j < N → time j < time (j+1)) ∧
      (∀ j, j ≤ N → 0 < time j ∧ time j < 1 ∧
        ∀ i q, q ≠ pick j i →
          a i q+time j*b i q < a i (pick j i)+time j*b i (pick j i)) ∧
      (∀ j, j < N → pick j ≠ pick (j+1)) ∧
      (∀ j, j < N → ∃ u : ℝ, time j < u ∧ u < time (j+1) ∧
        (∀ i q, a i q+u*b i q ≤ a i (pick j i)+u*b i (pick j i)) ∧
        (∀ i, a i (pick (j+1) i)+u*b i (pick (j+1) i) =
          a i (pick j i)+u*b i (pick j i))) := by
  classical
  obtain ⟨N, time, pick, h0, h1, hinc, hmax, hne, hwall⟩ :=
    exists_itinerary m k a b p0 p1 ha hp0 hp1
  refine ⟨N, time, pick, h0, h1, hinc, hmax, hne, ?_⟩
  intro j hj
  obtain ⟨u, _, _, hw, he⟩ := hwall j hj
  have hc : ∃ i, pick j i ≠ pick (j+1) i := by
    by_contra hn
    push_neg at hn
    exact hne j hj (funext hn)
  obtain ⟨i, hi⟩ := hc
  have hs := (hmax j (by omega)).2.2 i (pick (j+1) i) (Ne.symm hi)
  have ht := (hmax (j+1) (by omega)).2.2 i (pick j i) hi
  have hh := root_between
    (a i (pick (j+1) i)-a i (pick j i))
    (b i (pick (j+1) i)-b i (pick j i))
    (time j) (time (j+1)) u (hinc j hj)
    (by nlinarith) (by nlinarith) (by have hh := he i; nlinarith)
  exact ⟨u, hh.1, hh.2, hw, he⟩

#print axioms root_between
#print axioms crossing_sequence
end Hirsch.FiniteAffineChambers

-- The following slope-count proof is reused from accepted #239.
-- Only its enclosing namespace and public declaration name are changed.
namespace Hirsch.FiniteAffineChambers.Count

private def slopeRank {V : Type*} [Fintype V] (b : V → ℝ) (q : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p => b p < b q)).card

private theorem slopeRank_lt_card {V : Type*} [Fintype V]
    (b : V → ℝ) (q : V) : slopeRank b q < Fintype.card V := by
  classical
  let s := Finset.univ.filter (fun p => b p < b q)
  have hsub : s ⊂ (Finset.univ : Finset V) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
    intro he
    have hq : q ∈ s := by rw [he]; exact Finset.mem_univ q
    have hlt : b q < b q := (Finset.mem_filter.mp hq).2
    exact (lt_irrefl _) hlt
  exact Finset.card_lt_card hsub

private theorem slopeRank_mono {V : Type*} [Fintype V]
    (b : V → ℝ) (p q : V) (h : b p ≤ b q) : slopeRank b p ≤ slopeRank b q := by
  classical
  apply Finset.card_le_card
  intro v hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le (Finset.mem_filter.mp hv).2 h⟩

private theorem slopeRank_strict {V : Type*} [Fintype V]
    (b : V → ℝ) (p q : V) (h : b p < b q) : slopeRank b p < slopeRank b q := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans (Finset.mem_filter.mp hv).2 h⟩
  · intro he
    have hp : p ∈ Finset.univ.filter (fun v => b v < b q) := by simp [h]
    rw [← he] at hp
    exact (lt_irrefl _) (Finset.mem_filter.mp hp).2

private theorem changed_maximizer_slope {V : Type*}
    (a b : V → ℝ) (p q : V) (s t : ℝ) (hst : s < t)
    (hleft : a q + s*b q < a p + s*b p)
    (hright : a p + t*b p < a q + t*b q) : b p < b q := by
  by_contra hn
  have hb : b q ≤ b p := le_of_not_gt hn
  have hp := mul_nonneg (sub_nonneg.mpr hst.le) (sub_nonneg.mpr hb)
  nlinarith

theorem switch_bound
    (r N : ℕ) (k : Fin r → ℕ)
    (a b : (i : Fin r) → Fin (k i) → ℝ)
    (pick : ℕ → (i : Fin r) → Fin (k i)) (time : ℕ → ℝ)
    (hinc : ∀ j, j < N → time j < time (j+1))
    (hmax : ∀ j, j ≤ N → ∀ i q, q ≠ pick j i →
      a i q + time j*b i q < a i (pick j i) + time j*b i (pick j i))
    (hchange : ∀ j, j < N → ∃ i, pick j i ≠ pick (j+1) i) :
    N ≤ ∑ i, (k i - 1) := by
  classical
  let rank : ℕ → Fin r → ℕ := fun j i => slopeRank (b i) (pick j i)
  have hstep : ∀ j, j < N → (∑ i, rank j i) < ∑ i, rank (j+1) i := by
    intro j hj
    have hslope : ∀ i, pick j i ≠ pick (j+1) i → b i (pick j i) < b i (pick (j+1) i) := by
      intro i hi
      exact changed_maximizer_slope (a i) (b i) (pick j i) (pick (j+1) i)
        (time j) (time (j+1)) (hinc j hj)
        (hmax j (by omega) i (pick (j+1) i) (Ne.symm hi))
        (hmax (j+1) (by omega) i (pick j i) hi)
    apply Finset.sum_lt_sum
    · intro i _
      by_cases hi : pick j i = pick (j+1) i
      · simp only [rank, hi]
        exact le_rfl
      · exact slopeRank_mono (b i) _ _ (hslope i hi).le
    · obtain ⟨i, hi⟩ := hchange j hj
      exact ⟨i, Finset.mem_univ _, slopeRank_strict (b i) _ _ (hslope i hi)⟩
  have hgrow : ∀ j, j ≤ N → j ≤ ∑ i, rank j i := by
    intro j
    induction j with
    | zero => intro _; exact Nat.zero_le _
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hnext := hstep j (by omega)
      omega
  have htop : (∑ i, rank N i) ≤ ∑ i, (k i - 1) := by
    apply Finset.sum_le_sum
    intro i _
    have h := slopeRank_lt_card (b i) (pick N i)
    simp only [Fintype.card_fin] at h
    change slopeRank (b i) (pick N i) ≤ k i - 1
    omega
  exact (hgrow N le_rfl).trans htop
end Hirsch.FiniteAffineChambers.Count

/-- Construct the bounded finite envelope itinerary, rather than assuming its
sample times, crossing list, unique interval winners or wall certificates. -/
theorem solution
    (m : ℕ) (k : Fin m → ℕ)
    (a b : (i : Fin m) → Fin (k i) → ℝ)
    (p0 p1 : (i : Fin m) → Fin (k i))
    (ha : ∀ i, Function.Injective (a i))
    (hp0 : ∀ i q, q ≠ p0 i → a i q < a i (p0 i))
    (hp1 : ∀ i q, q ≠ p1 i → a i q + b i q < a i (p1 i) + b i (p1 i)) :
    ∃ (N : ℕ) (time : ℕ → ℝ)
      (pick : ℕ → (i : Fin m) → Fin (k i)),
      N ≤ ∑ i, (k i-1) ∧ pick 0 = p0 ∧ pick N = p1 ∧
      (∀ j, j < N → time j < time (j+1)) ∧
      (∀ j, j ≤ N → 0 < time j ∧ time j < 1 ∧
        ∀ i q, q ≠ pick j i →
          a i q+time j*b i q < a i (pick j i)+time j*b i (pick j i)) ∧
      (∀ j, j < N → pick j ≠ pick (j+1)) ∧
      (∀ j, j < N → ∃ u : ℝ, time j < u ∧ u < time (j+1) ∧
        (∀ i q, a i q+u*b i q ≤ a i (pick j i)+u*b i (pick j i)) ∧
        (∀ i, a i (pick (j+1) i)+u*b i (pick (j+1) i) =
          a i (pick j i)+u*b i (pick j i))) := by
  classical
  obtain ⟨N, time, pick, h0, h1, hinc, hmax, hne, hwall⟩ :=
    Hirsch.FiniteAffineChambers.crossing_sequence m k a b p0 p1 ha hp0 hp1
  have hchange : ∀ j, j < N → ∃ i, pick j i ≠ pick (j+1) i := by
    intro j hj
    by_contra hn
    push_neg at hn
    exact hne j hj (funext hn)
  have hb := Hirsch.FiniteAffineChambers.Count.switch_bound m N k a b pick time hinc
    (fun j hj => (hmax j hj).2.2) hchange
  exact ⟨N, time, pick, hb, h0, h1, hinc, hmax, hne, hwall⟩

#print axioms solution
