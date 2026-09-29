-- Prove2me | solution 1 for TropicalLA.eigen_isTropicalRoot
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T11:01:20.29623+00:00
-- url     : https://prove2.me/submissions/4ef62a51-4e54-4042-bd88-f9701ede6c08

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalCharPoly
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue

open Finset TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Nonempty ι] {A : Matrix ι ι ℝ}
    {lam : ℝ} {v : ι → ℝ} (h : IsTropEigen A lam v) :
    IsTropicalRoot A lam ∧ charPolyVal A lam = (Fintype.card ι : ℝ) * lam := by
  classical
  have hle : ∀ k : ℕ, k ≤ Fintype.card ι → charCoeff A k ≤ k * lam := by
    intro k hk
    have hne : (admPairs ι k).Nonempty := by
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
        (show k ≤ (univ : Finset ι).card by simpa using hk)
      exact ⟨(s, 1), by simp [admPairs, hs]⟩
    unfold charCoeff
    rw [dif_pos hne]
    apply Finset.sup'_le
    rintro ⟨s, σ⟩ hp
    simp only [admPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hcard, hmaps⟩ := hp
    dsimp only
    -- every edge is dominated by the eigen-equation
    have hedge : ∀ i, A i (σ i) ≤ lam + v i - v (σ i) := by
      intro i
      have h1 := Finset.le_sup' (fun j => A i j + v j) (mem_univ (σ i))
      have h2 : univ.sup' univ_nonempty (fun j => A i j + v j) = lam + v i := h i
      simp only at h1
      linarith
    -- `σ` permutes `s`, so the potential terms cancel
    have himage : s.image σ = s := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
        exact hmaps y hy
      · simp [Finset.card_image_of_injective _ σ.injective]
    have hsum : ∑ i ∈ s, v (σ i) = ∑ i ∈ s, v i := by
      rw [← Finset.sum_image (f := v) (g := σ) (fun x _ y _ hxy => σ.injective hxy), himage]
    unfold minorWeight
    calc ∑ i ∈ s, A i (σ i) ≤ ∑ i ∈ s, (lam + v i - v (σ i)) :=
          Finset.sum_le_sum fun i _ => hedge i
      _ = k * lam := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum, Finset.sum_const, hcard,
          nsmul_eq_mul]
        ring
  have hexk : ∃ k : ℕ, 0 < k ∧ k ≤ Fintype.card ι ∧ charCoeff A k = k * lam := by
    obtain ⟨f, y, p, hp, hper, hmin, hf⟩ := h.exists_minimal_periodic_point
    -- the orbit of `y` has exactly `p` points
    have hinj : ∀ a b, a < p → b < p → f^[a] y = f^[b] y → a = b := by
      have key : ∀ a b, a < b → b < p → f^[a] y = f^[b] y → False := by
        intro a b hab hb hfab
        have e : f^[p - a] (f^[a] y) = f^[p - a] (f^[b] y) := by rw [hfab]
        rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
          show p - a + a = p by omega, hper, show p - a + b = (b - a) + p by omega,
          Function.iterate_add_apply, hper] at e
        exact hmin (b - a) (by omega) (by omega) e.symm
      intro a b ha hb hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact key a b hlt hb hab
      · exact key b a hlt ha hab.symm
    have hback : ∀ a, f^[p - 1] (f^[a + 1] y) = f^[a] y := by
      intro a
      rw [← Function.iterate_add_apply, show p - 1 + (a + 1) = a + p by omega,
        Function.iterate_add_apply, hper]
    have hinjf : ∀ a b, a < p → b < p → f (f^[a] y) = f (f^[b] y) → a = b := by
      intro a b ha hb hab
      apply hinj a b ha hb
      rw [← hback a, ← hback b, Function.iterate_succ_apply', Function.iterate_succ_apply', hab]
    set s : Finset ι := (range p).image (fun t => f^[t] y) with hs
    have hmem : ∀ x, x ∈ s ↔ ∃ t, t < p ∧ f^[t] y = x := by
      intro x
      simp [hs]
    have hcard : s.card = p := by
      rw [hs, Finset.card_image_of_injOn, Finset.card_range]
      intro a ha b hb hab
      exact hinj a b (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) hab
    have hfs : ∀ x ∈ s, f x ∈ s := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := (hmem x).1 hx
      rw [hmem]
      rcases Nat.lt_or_ge (t + 1) p with h1 | h1
      · exact ⟨t + 1, h1, Function.iterate_succ_apply' f t y⟩
      · refine ⟨0, hp, ?_⟩
        rw [show p = t + 1 by omega] at hper
        rw [← Function.iterate_succ_apply' f t y, hper]
        rfl
    have hfinj : ∀ x ∈ s, ∀ x' ∈ s, f x = f x' → x = x' := by
      intro x hx x' hx' hxx
      obtain ⟨a, ha, rfl⟩ := (hmem x).1 hx
      obtain ⟨b, hb, rfl⟩ := (hmem x').1 hx'
      rw [hinjf a b ha hb hxx]
    -- the cyclic permutation of the orbit
    set g : ι → ι := fun x => if x ∈ s then f x else x with hg
    have hginj : Function.Injective g := by
      intro x x' hxx
      by_cases hx : x ∈ s <;> by_cases hx' : x' ∈ s
      · simp only [hg, hx, hx', if_true] at hxx
        exact hfinj x hx x' hx' hxx
      · simp only [hg, hx, hx', if_true, if_false] at hxx
        exact absurd (hxx ▸ hfs x hx) hx'
      · simp only [hg, hx, hx', if_true, if_false] at hxx
        exact absurd (hxx ▸ hfs x' hx') hx
      · simpa [hg, hx, hx'] using hxx
    set σ : Equiv.Perm ι := Equiv.ofBijective g (Finite.injective_iff_bijective.1 hginj) with hσ
    have hσs : ∀ x ∈ s, σ x = f x := by
      intro x hx
      simp [hσ, hg, hx]
    have hadm : (s, σ) ∈ admPairs ι p := by
      simp only [admPairs, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hcard, fun x hx => ?_⟩
      rw [hσs x hx]
      exact hfs x hx
    -- its weight is exactly `p * lam`
    have himage : s.image σ = s := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
        rw [hσs z hz]
        exact hfs z hz
      · simp [Finset.card_image_of_injective _ σ.injective]
    have hsum : ∑ x ∈ s, v (σ x) = ∑ x ∈ s, v x := by
      rw [← Finset.sum_image (f := v) (g := σ) (fun x _ z _ hxz => σ.injective hxz), himage]
    have hw : minorWeight A s σ = p * lam := by
      unfold minorWeight
      have e : ∀ x ∈ s, A x (σ x) = lam + v x - v (σ x) := by
        intro x hx
        rw [hσs x hx]
        linarith [hf x]
      rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum,
        Finset.sum_const, hcard, nsmul_eq_mul]
      ring
    have hpn : p ≤ Fintype.card ι := by
      rw [← hcard]
      exact Finset.card_le_univ s
    refine ⟨p, hp, hpn, le_antisymm (hle p hpn) ?_⟩
    unfold charCoeff
    rw [dif_pos ⟨_, hadm⟩, ← hw]
    exact Finset.le_sup' (fun q : Finset ι × Equiv.Perm ι => minorWeight A q.1 q.2) hadm
  have hc0 : charCoeff A 0 = 0 := by
    unfold charCoeff
    split_ifs with hne
    · apply le_antisymm
      · apply Finset.sup'_le
        rintro ⟨s, σ⟩ hsσ
        simp only [admPairs, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.card_eq_zero] at hsσ
        obtain ⟨rfl, -⟩ := hsσ
        simp [minorWeight]
      · refine le_trans (le_of_eq ?_) (Finset.le_sup'
          (fun q : Finset ι × Equiv.Perm ι => minorWeight A q.1 q.2)
          (show ((∅ : Finset ι), (1 : Equiv.Perm ι)) ∈ admPairs ι 0 by simp [admPairs]))
        simp [minorWeight]
    · rfl
  have hval : charPolyVal A lam = (Fintype.card ι : ℝ) * lam := by
    unfold charPolyVal
    apply le_antisymm
    · apply Finset.sup'_le
      intro k hk
      have hk' : k ≤ Fintype.card ι := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have := hle k hk'
      linarith
    · refine le_trans (le_of_eq ?_) (Finset.le_sup'
        (fun k => charCoeff A k + ((Fintype.card ι : ℝ) - k) * lam)
        (Finset.mem_range.2 (Nat.succ_pos _)))
      simp [hc0]
  have hroot : IsTropicalRoot A lam := by
    obtain ⟨k, hk, hkn, hkc⟩ := hexk
    refine ⟨0, k, Nat.zero_le _, hkn, by omega, ?_, ?_⟩
    · rw [hval, hc0]
      push_cast
      ring
    · rw [hval, hkc]
      ring
  exact ⟨hroot, hval⟩
