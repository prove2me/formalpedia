-- Prove2me | solution 2 for Geometry.KernelPatterns.card_ordPatternsWith
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T19:01:42.113079+00:00
-- url     : https://prove2.me/submissions/6756505d-e76d-4158-aa88-7c1dfacb68ae

import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Bell
import Definitions.Def_Geometry_KernelPatterns_Core
import Definitions.Def_Geometry_KernelPatterns_Stirling
import Definitions.Def_Geometry_KernelPatterns_BellRecursion
import Definitions.Def_Geometry_KernelPatterns_Faces
import Definitions.Def_Geometry_KernelPatterns_Fubini

open Geometry.KernelPatterns Finset in
theorem solution (n k : ℕ) :
    (ordPatternsWith n k).card = Nat.stirlingSecond n k * k.factorial := by
  classical
  have hstir : ∀ n k : ℕ, (patternsWith n k).card = Nat.stirlingSecond n k := by
    -- Pascal splitting of a binomial sum
    have hpas : ∀ (g : ℕ → ℕ) (m : ℕ), ∑ i ∈ range (m + 2), (m + 1).choose i * g i
        = ∑ i ∈ range (m + 1), m.choose i * g (i + 1) + ∑ i ∈ range (m + 1), m.choose i * g i := by
      intro g m
      rw [Finset.sum_range_succ']
      simp only [Nat.choose_succ_succ, add_mul, Finset.sum_add_distrib, Nat.choose_zero_right]
      have h1 : ∑ i ∈ range (m + 1), m.choose (i + 1) * g (i + 1)
          = ∑ i ∈ range m, m.choose (i + 1) * g (i + 1) := by
        rw [Finset.sum_range_succ, Nat.choose_succ_self, zero_mul, add_zero]
      have h2 : ∑ i ∈ range (m + 1), m.choose i * g i
          = ∑ i ∈ range m, m.choose (i + 1) * g (i + 1) + 1 * g 0 := by
        rw [Finset.sum_range_succ', Nat.choose_zero_right]
      rw [h1, h2]
      ring
    -- `S(n+1, k+1) = ∑_i C(n, i) S(i, k)`
    have hD : ∀ m k : ℕ, Nat.stirlingSecond (m + 1) (k + 1)
        = ∑ i ∈ range (m + 1), m.choose i * Nat.stirlingSecond i k := by
      intro m
      induction m with
      | zero =>
        intro k
        cases k with
        | zero => simp [Nat.stirlingSecond]
        | succ k => simp [Nat.stirlingSecond]
      | succ m ih =>
        intro k
        rw [hpas (fun i => Nat.stirlingSecond i k) m, ← ih k]
        cases k with
        | zero =>
          simp only [Nat.stirlingSecond_succ_zero, mul_zero, Finset.sum_const_zero, zero_add]
          rw [Nat.stirlingSecond_one_right, Nat.stirlingSecond_one_right]
        | succ k =>
          have hsum : ∑ i ∈ range (m + 1), m.choose i * Nat.stirlingSecond (i + 1) (k + 1)
              = (k + 1) * Nat.stirlingSecond (m + 1) (k + 1 + 1)
                + Nat.stirlingSecond (m + 1) (k + 1) := by
            rw [ih (k + 1), ih k, Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Nat.stirlingSecond_succ_succ]
            ring
          rw [hsum, Nat.stirlingSecond_succ_succ (m + 1) (k + 1)]
          ring
    -- image size = number of kernel classes
    have hG : ∀ {m : ℕ} {X : Type} [DecidableEq X] (f : Fin m → X),
        (univ.image f).card = Nat.card (Quotient (Setoid.ker f)) := by
      intro m X _ f
      rw [Nat.card_congr (Setoid.quotientKerEquivRange f), Nat.card_eq_card_toFinset,
        Set.toFinset_range]
    -- the pattern attached to `(S, t)` has one block more than `t`
    have hpatS : ∀ {m : ℕ} (S : Finset (Fin m)) (t : Setoid ↥(Sᶜ)),
        (univ.image (patternOfSetoid S t)).card = Nat.card (Quotient t) + 1 := by
      intro m S t
      rw [hG]
      have hk : Setoid.ker (patternOfSetoid S t) = Setoid.ker (blockFun S t) :=
        Setoid.ext fun a b => patternOfSetoid_eq_iff S t a b
      rw [hk, Nat.card_congr (Setoid.quotientKerEquivRange _)]
      have hsurj : Set.range (blockFun S t) = Set.univ := by
        apply Set.eq_univ_of_forall
        rintro (_ | q)
        · exact ⟨Fin.last m, blockFun_last S t⟩
        · obtain ⟨x, rfl⟩ := Quotient.exists_rep q
          exact ⟨(x : Fin m).castSucc, blockFun_castSucc_of_not_mem t (Finset.mem_compl.1 x.2)⟩
      rw [hsurj, Nat.card_univ, Finite.card_option]
    -- patterns with `k` blocks = setoids with `k` classes
    have hPW : ∀ m k : ℕ, (patternsWith m k).card
        = Nat.card {s : Setoid (Fin m) // Nat.card (Quotient s) = k} := by
      intro m k
      rw [← Nat.card_eq_finsetCard]
      apply Nat.card_congr
      refine (?_ : ↥(patternsWith m k) ≃ {p : ↥(patterns m m) // (univ.image (p : Fin m → Fin m)).card = k}).trans
        (Equiv.subtypeEquiv (patternsEquivSetoid m) (fun p => ?_))
      · exact { toFun := fun p => ⟨⟨p.1, (Finset.mem_filter.1 p.2).1⟩, (Finset.mem_filter.1 p.2).2⟩
                invFun := fun p => ⟨p.1.1, Finset.mem_filter.2 ⟨p.1.2, p.2⟩⟩
                left_inv := fun p => rfl
                right_inv := fun p => rfl }
      · rw [hG]
        exact Iff.rfl
    -- the fibre over `S` with `k + 1` blocks = setoids on `Sᶜ` with `k` classes
    have hFib : ∀ (m k : ℕ) (S : Finset (Fin m)),
        ((lastBlkFibre m S).filter (fun p => (univ.image p).card = k + 1)).card
          = Nat.card {t : Setoid ↥(Sᶜ) // Nat.card (Quotient t) = k} := by
      intro m k S
      rw [← Nat.card_eq_finsetCard]
      apply Nat.card_congr
      refine (?_ : ↥((lastBlkFibre m S).filter (fun p => (univ.image p).card = k + 1))
          ≃ {p : ↥(lastBlkFibre m S) // (univ.image (p : Fin (m + 1) → Fin (m + 1))).card = k + 1}).trans
        (Equiv.subtypeEquiv (lastBlkFibreEquiv m S) (fun p => ?_))
      · exact { toFun := fun p => ⟨⟨p.1, (Finset.mem_filter.1 p.2).1⟩, (Finset.mem_filter.1 p.2).2⟩
                invFun := fun p => ⟨p.1.1, Finset.mem_filter.2 ⟨p.1.2, p.2⟩⟩
                left_inv := fun p => rfl
                right_inv := fun p => rfl }
      · have hp : (p : Fin (m + 1) → Fin (m + 1))
            = patternOfSetoid S (lastBlkFibreEquiv m S p) := by
          conv_lhs => rw [← (lastBlkFibreEquiv m S).symm_apply_apply p]
          rfl
        rw [hp, hpatS]
        omega
    -- class counts are invariant under relabelling
    have hTr : ∀ {α β : Type} (e : α ≃ β) (k : ℕ),
        Nat.card {t : Setoid α // Nat.card (Quotient t) = k}
          = Nat.card {t : Setoid β // Nat.card (Quotient t) = k} := by
      intro α β e k
      apply Nat.card_congr
      refine Equiv.subtypeEquiv (setoidCongr e) (fun t => ?_)
      have h : Nat.card (Quotient (setoidCongr e t)) = Nat.card (Quotient t) :=
        Nat.card_congr (Quotient.congr e.symm (fun a b => Iff.rfl))
      rw [h]
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro k
      rcases n with _ | m
      · rcases k with _ | k
        · rw [Nat.stirlingSecond_zero, Finset.card_eq_one]
          refine ⟨Fin.elim0, ?_⟩
          ext f
          simp only [Finset.mem_singleton]
          constructor
          · intro _
            funext i
            exact i.elim0
          · rintro rfl
            rw [patternsWith, Finset.mem_filter]
            exact ⟨(mem_patterns_self _).2 (funext fun i => i.elim0), by simp⟩
        · rw [Nat.stirlingSecond_zero_succ, Finset.card_eq_zero, patternsWith,
            Finset.filter_eq_empty_iff]
          intro p _
          simp
      · rcases k with _ | k
        · rw [Nat.stirlingSecond_succ_zero, Finset.card_eq_zero, patternsWith,
            Finset.filter_eq_empty_iff]
          intro p _ h
          have : 0 < (univ.image p).card := Finset.card_pos.2 (Finset.univ_nonempty.image p)
          omega
        · have hfib : (patternsWith (m + 1) (k + 1)).card
              = ∑ S : Finset (Fin m),
                  ((lastBlkFibre m S).filter (fun p => (univ.image p).card = k + 1)).card := by
            rw [Finset.card_eq_sum_card_fiberwise (f := lastBlk) (t := univ)
              (fun p _ => Finset.mem_coe.2 (Finset.mem_univ (lastBlk p)))]
            refine Finset.sum_congr rfl fun S _ => ?_
            congr 1
            ext p
            simp only [patternsWith, lastBlkFibre, Finset.mem_filter]
            tauto
          have hS : ∀ S : Finset (Fin m),
              ((lastBlkFibre m S).filter (fun p => (univ.image p).card = k + 1)).card
                = (patternsWith (m - S.card) k).card := by
            intro S
            rw [hFib, hTr (Fintype.equivFin ↥(Sᶜ)) k, ← hPW, Fintype.card_coe, Finset.card_compl,
              Fintype.card_fin]
          rw [hfib, Finset.sum_congr rfl fun S _ => hS S,
            Finset.sum_congr rfl fun S _ => ih (m - S.card) (by omega) k,
            ← Finset.powerset_univ,
            Finset.sum_powerset_apply_card (fun j => Nat.stirlingSecond (m - j) k),
            Finset.card_univ, Fintype.card_fin, hD m k]
          conv_rhs => rw [← Finset.sum_range_reflect]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [Finset.mem_range] at hj
          rw [smul_eq_mul, show m + 1 - 1 - j = m - j by omega, Nat.choose_symm (by omega)]
  -- image size = number of kernel classes
  have hG : ∀ {X : Type} [DecidableEq X] (f : Fin n → X),
      (univ.image f).card = Nat.card (Quotient (Setoid.ker f)) := by
    intro X _ f
    rw [Nat.card_congr (Setoid.quotientKerEquivRange f), Nat.card_eq_card_toFinset,
      Set.toFinset_range]
  have hpatcard : ∀ {X : Type} [DecidableEq X] (f : Fin n → X),
      (univ.image (pat f)).card = (univ.image f).card := by
    intro X _ f
    rw [hG, hG]
    have hk : Setoid.ker (pat f) = Setoid.ker f := Setoid.ext fun a b => pat_eq_iff
    rw [hk]
  -- initial segments of `Fin n`
  have hseg : ∀ a, a ≤ n → #(univ.filter (fun i : Fin n => (i : ℕ) < a)) = a := by
    intro a ha
    apply le_antisymm
    · have h1 := Finset.card_le_card_of_injOn (fun v : Fin n => (v : ℕ))
        (s := univ.filter (fun i : Fin n => (i : ℕ) < a)) (t := Finset.range a)
        (fun v hv => by
          rw [Finset.mem_coe, Finset.mem_filter] at hv
          rw [Finset.mem_coe, Finset.mem_range]
          exact hv.2)
        (fun x _ y _ hxy => Fin.ext hxy)
      rwa [Finset.card_range] at h1
    · have hsub : (univ : Finset (Fin a)).image (Fin.castLE ha)
          ⊆ univ.filter (fun i : Fin n => (i : ℕ) < a) := by
        intro w hw
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hw
        simp [i.isLt]
      have h5 := Finset.card_le_card hsub
      rwa [Finset.card_image_of_injective _ (Fin.castLE_injective _), Finset.card_univ,
        Fintype.card_fin] at h5
  -- block representatives
  have hrepsmem : ∀ {X : Type} [LinearOrder X] (v : Fin n → X) (j : Fin n),
      j ∈ reps v ↔ pat v j = j := by
    intro X _ v j
    simp [reps]
  have hrep_inj : ∀ {X : Type} [LinearOrder X] (v : Fin n → X) (j1 j2 : Fin n),
      j1 ∈ reps v → j2 ∈ reps v → v j1 = v j2 → j1 = j2 := by
    intro X _ v j1 j2 h1 h2 h
    rw [hrepsmem] at h1 h2
    rw [← h1, ← h2]
    exact pat_eq_iff.2 h
  have hpat_rep : ∀ {X : Type} [LinearOrder X] (v : Fin n → X) (i : Fin n), pat v i ∈ reps v := by
    intro X _ v i
    rw [hrepsmem]
    exact pat_apply_pat v i
  have hrank : ∀ {X : Type} [LinearOrder X] (v : Fin n → X) (i : Fin n),
      (rank v i : ℕ) = #((reps v).filter (fun j => v j < v i)) := by
    intro X _ v i
    show #(univ.filter fun j => pat v j = j ∧ v j < v i) = _
    rw [reps, Finset.filter_filter]
  -- the image of a rank function is an initial segment
  have himg : ∀ {X : Type} [LinearOrder X] (v : Fin n → X),
      univ.image (rank v) = univ.filter (fun i : Fin n => (i : ℕ) < #(reps v)) := by
    intro X _ v
    have hsub : univ.image (rank v) ⊆ univ.filter (fun i : Fin n => (i : ℕ) < #(reps v)) := by
      intro r hr
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hr
      rw [Finset.mem_filter]
      refine ⟨mem_univ _, ?_⟩
      rw [hrank]
      apply Finset.card_lt_card
      refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
      have h1 := h (hpat_rep v i)
      rw [Finset.mem_filter, apply_pat v i] at h1
      exact lt_irrefl _ h1.2
    have hlt : ∀ j1 ∈ reps v, ∀ j2 ∈ reps v, v j1 < v j2 → (rank v j1 : ℕ) < rank v j2 := by
      intro j1 h1 j2 h2 hlt
      rw [hrank, hrank]
      apply Finset.card_lt_card
      refine ⟨fun j hj => ?_, fun h => ?_⟩
      · rw [Finset.mem_filter] at hj ⊢
        exact ⟨hj.1, hj.2.trans hlt⟩
      · have h3 := h (Finset.mem_filter.2 ⟨h1, hlt⟩)
        rw [Finset.mem_filter] at h3
        exact lt_irrefl _ h3.2
    have hinj : Set.InjOn (rank v) (reps v) := by
      intro j1 h1 j2 h2 heq
      rw [Finset.mem_coe] at h1 h2
      by_contra hne
      have hv : v j1 ≠ v j2 := fun h => hne (hrep_inj v j1 j2 h1 h2 h)
      rcases lt_or_gt_of_ne hv with hl | hl
      · have := hlt j1 h1 j2 h2 hl
        rw [heq] at this
        exact lt_irrefl _ this
      · have := hlt j2 h2 j1 h1 hl
        rw [heq] at this
        exact lt_irrefl _ this
    have hcard : #((reps v).image (rank v)) = #(reps v) := Finset.card_image_of_injOn hinj
    have hsub2 : (reps v).image (rank v) ⊆ univ.image (rank v) :=
      Finset.image_subset_image (subset_univ _)
    have hle : #(reps v) ≤ n := by simpa using Finset.card_le_univ (reps v)
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hseg _ hle, ← hcard]
    exact Finset.card_le_card hsub2
  -- ordered patterns with `k` blocks are exactly the maps onto `{0, …, k-1}`
  have hmem : ∀ r : Fin n → Fin n, r ∈ ordPatternsWith n k ↔
      k ≤ n ∧ univ.image r = univ.filter (fun i : Fin n => (i : ℕ) < k) := by
    intro r
    simp only [ordPatternsWith, ordPatterns, Finset.mem_filter, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨v, rfl⟩, hk⟩
      have hle : #(reps v) ≤ n := by simpa using Finset.card_le_univ (reps v)
      rw [himg v, hseg _ hle] at hk
      refine ⟨hk ▸ hle, ?_⟩
      rw [himg v, hk]
    · rintro ⟨hkn, himr⟩
      refine ⟨⟨r, ?_⟩, by rw [himr, hseg k hkn]⟩
      funext i
      apply Fin.ext
      rw [hrank]
      have hbij : ((reps r).filter (fun j => r j < r i)).image r
          = univ.filter (fun m : Fin n => (m : ℕ) < (r i : ℕ)) := by
        ext m
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨j, ⟨-, hj⟩, rfl⟩
          exact hj
        · intro hm
          have hri : (r i : ℕ) < k := by
            have : r i ∈ univ.image r := Finset.mem_image_of_mem r (mem_univ i)
            rw [himr, Finset.mem_filter] at this
            exact this.2
          have hmimg : m ∈ univ.image r := by
            rw [himr, Finset.mem_filter]
            exact ⟨mem_univ _, by omega⟩
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hmimg
          exact ⟨pat r j, ⟨hpat_rep r j, by rw [apply_pat r j]; exact hm⟩, apply_pat r j⟩
      have hinj : Set.InjOn r ((reps r).filter (fun j => r j < r i)) :=
        fun j1 h1 j2 h2 h => hrep_inj r j1 j2 (Finset.mem_filter.1 h1).1
          (Finset.mem_filter.1 h2).1 h
      rw [← Finset.card_image_of_injOn hinj, hbij]
      exact hseg _ (le_of_lt (r i).isLt)
  -- each fibre of `pat` has `k!` elements
  have hfibre : ∀ p ∈ patternsWith n k, k ≤ n →
      #((ordPatternsWith n k).filter (fun r => pat r = p)) = k.factorial := by
    intro p hp hkn
    rw [patternsWith, Finset.mem_filter, mem_patterns_self] at hp
    obtain ⟨hpp, hpk⟩ := hp
    have hidem : ∀ i, p (p i) = p i := by
      intro i
      have := pat_apply_pat p i
      rw [hpp] at this
      exact this
    set seg := univ.filter (fun i : Fin n => (i : ℕ) < k) with hseg_def
    have hsegc : #seg = k := hseg k hkn
    -- from an ordered pattern over `p` to a bijection `image p ≃ seg`
    have hker : ∀ r : Fin n → Fin n, pat r = p → ∀ x y, r x = r y ↔ p x = p y := by
      intro r hr x y
      rw [← hr, pat_eq_iff]
    have toFunB : ∀ r : ↥((ordPatternsWith n k).filter (fun r => pat r = p)),
        Function.Bijective (fun b : ↥(univ.image p) =>
          (⟨(r : Fin n → Fin n) b, by
            have hr := (Finset.mem_filter.1 r.2)
            rw [← ((hmem _).1 hr.1).2]
            exact Finset.mem_image_of_mem _ (mem_univ _)⟩ : ↥seg)) := by
      intro r
      have hr := Finset.mem_filter.1 r.2
      constructor
      · rintro ⟨b1, hb1⟩ ⟨b2, hb2⟩ h
        simp only [Subtype.mk.injEq] at h
        obtain ⟨i1, -, rfl⟩ := Finset.mem_image.1 hb1
        obtain ⟨i2, -, rfl⟩ := Finset.mem_image.1 hb2
        apply Subtype.ext
        have h' := (hker _ hr.2 _ _).1 h
        rw [hidem, hidem] at h'
        exact h'
      · rintro ⟨m, hm⟩
        rw [← ((hmem _).1 hr.1).2] at hm
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hm
        refine ⟨⟨p i, Finset.mem_image_of_mem _ (mem_univ _)⟩, ?_⟩
        apply Subtype.ext
        show (r : Fin n → Fin n) (p i) = (r : Fin n → Fin n) i
        have h7 := apply_pat (r : Fin n → Fin n) i
        rw [hr.2] at h7
        exact h7
    let e : ↥((ordPatternsWith n k).filter (fun r => pat r = p)) ≃ (↥(univ.image p) ≃ ↥seg) :=
      { toFun := fun r => Equiv.ofBijective _ (toFunB r)
        invFun := fun φ => ⟨fun i => (φ ⟨p i, Finset.mem_image_of_mem _ (mem_univ _)⟩ : Fin n), by
          rw [Finset.mem_filter]
          have hkerφ : ∀ x y, (φ ⟨p x, Finset.mem_image_of_mem _ (mem_univ _)⟩ : Fin n)
              = (φ ⟨p y, Finset.mem_image_of_mem _ (mem_univ _)⟩ : Fin n) ↔ p x = p y := by
            intro x y
            rw [Subtype.coe_inj, φ.apply_eq_iff_eq, Subtype.mk.injEq]
          refine ⟨(hmem _).2 ⟨hkn, ?_⟩, ?_⟩
          · ext m
            simp only [Finset.mem_image, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨i, rfl⟩
              exact (φ _).2
            · intro hm
              obtain ⟨⟨b, hb⟩, hφb⟩ := φ.surjective ⟨m, hm⟩
              obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hb
              refine ⟨i, ?_⟩
              rw [hφb]
          · exact (pat_congr fun x y => hkerφ x y).trans hpp⟩
        left_inv := fun r => by
          apply Subtype.ext
          funext i
          have hr := Finset.mem_filter.1 r.2
          show (r : Fin n → Fin n) (p i) = (r : Fin n → Fin n) i
          have h7 := apply_pat (r : Fin n → Fin n) i
          rw [hr.2] at h7
          exact h7
        right_inv := fun φ => by
          apply Equiv.ext
          rintro ⟨b, hb⟩
          apply Subtype.ext
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hb
          show (φ ⟨p (p i), _⟩ : Fin n) = (φ ⟨p i, hb⟩ : Fin n)
          congr 2
          exact Subtype.ext (hidem i) }
    rw [← Nat.card_eq_finsetCard, Nat.card_congr e, Nat.card_eq_fintype_card]
    have hc : Fintype.card ↥(univ.image p) = Fintype.card ↥seg := by
      rw [Fintype.card_coe, Fintype.card_coe, hpk, hsegc]
    rw [Fintype.card_equiv (Fintype.equivOfCardEq hc), Fintype.card_coe, hpk]
  by_cases hkn : k ≤ n
  · rw [Finset.card_eq_sum_card_fiberwise (f := pat) (t := patternsWith n k) (fun r hr => by
        rw [Finset.mem_coe] at hr ⊢
        rw [patternsWith, Finset.mem_filter, mem_patterns_self, pat_idem, hpatcard]
        refine ⟨rfl, ?_⟩
        rw [((hmem r).1 hr).2]
        exact hseg k hkn)]
    rw [Finset.sum_congr rfl (fun p hp => hfibre p hp hkn), Finset.sum_const, smul_eq_mul, hstir]
  · rw [Nat.stirlingSecond_eq_zero_of_lt (by omega), zero_mul, Finset.card_eq_zero,
      Finset.eq_empty_iff_forall_notMem]
    intro r hr
    exact hkn ((hmem r).1 hr).1
