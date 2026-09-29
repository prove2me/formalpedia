-- Prove2me | solution 2 for B3Free.exists_strongCopy_levelFamily
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T00:37:35.433546+00:00
-- url     : https://prove2.me/submissions/418ac9a7-ee1d-4bc0-9561-c52bfbaae054

import Mathlib
import Definitions.Def_Bridges_B3FreeFamilies
import Definitions.Def_Bridges_B3FreeFamiliesLevels

set_option maxHeartbeats 1000000 in
open B3Free Finset in
theorem solution {α : Type*} [DecidableEq α] [Fintype α] {d : ℕ} {S : Finset ℕ}
    (hS : d + 1 ≤ (S.filter (· ≤ Fintype.card α)).card) :
    ∃ ι : BoolLat d → Finset α, IsStrongCopy ι ∧ ∀ X, ι X ∈ levelFamily α S := by
  classical
  -- a base of size `a` inside `C`, together with `d` atoms of `C` outside it
  have exists_base_and_atoms : ∀ {a : ℕ} {C : Finset α}, a + d ≤ C.card →
      ∃ (s : Finset α) (f : Fin d → α), Function.Injective f ∧ (∀ i, f i ∉ s) ∧
        s.card = a ∧ s ⊆ C ∧ ∀ i, f i ∈ C := by
    intro a C hC
    obtain ⟨T, hTC, hTcard⟩ := Finset.le_card_iff_exists_subset_card.mp hC
    obtain ⟨s, hsT, hscard⟩ :=
      Finset.le_card_iff_exists_subset_card.mp (by omega : a ≤ T.card)
    have hUcard : (T \ s).card = d := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsT, hTcard, hscard]
      omega
    refine ⟨s, fun i => (((T \ s).equivFin.symm (finCongr hUcard.symm i) :
      {x // x ∈ T \ s}) : α), ?_, ?_, hscard, hsT.trans hTC, ?_⟩
    · intro i j hij
      exact (finCongr hUcard.symm).injective
        ((T \ s).equivFin.symm.injective (Subtype.ext hij))
    · intro i
      exact (Finset.mem_sdiff.mp ((T \ s).equivFin.symm (finCongr hUcard.symm i)).2).2
    · intro i
      exact hTC (Finset.mem_sdiff.mp ((T \ s).equivFin.symm (finCongr hUcard.symm i)).2).1
  -- the prescribed-cardinality construction (its own target is still open)
  have main : ∀ t : ℕ → ℕ, (∀ k < d, t k < t (k + 1)) → t d ≤ Fintype.card α →
      ∃ ι : BoolLat d → Finset α, IsStrongCopy ι ∧ ∀ X : BoolLat d, (ι X).card = t X.card := by
    intro t hstep hlast
    classical
    -- `t` is increasing on `[0, d]`, dominates the identity, and has increasing gaps
    have hmono : ∀ l, l ≤ d → ∀ k, k ≤ l → t k ≤ t l := by
      intro l
      induction l with
      | zero => intro _ k hk; have : k = 0 := by omega
                subst this; exact le_rfl
      | succ m ih =>
        intro hmd k hk
        rcases Nat.eq_or_lt_of_le hk with rfl | hlt
        · exact le_rfl
        · have h1 := ih (by omega) k (by omega)
          have h2 := hstep m (by omega)
          omega
    have hge : ∀ k, k ≤ d → k ≤ t k := by
      intro k
      induction k with
      | zero => intro _; omega
      | succ m ih =>
        intro hmd
        have h1 := ih (by omega)
        have h2 := hstep m (by omega)
        omega
    have hpad : ∀ l, l ≤ d → ∀ k, k ≤ l → t k - k ≤ t l - l := by
      intro l
      induction l with
      | zero => intro _ k hk; have : k = 0 := by omega
                subst this; exact le_rfl
      | succ m ih =>
        intro hmd k hk
        rcases Nat.eq_or_lt_of_le hk with rfl | hlt
        · exact le_rfl
        · have h1 := ih (by omega) k (by omega)
          have h2 := hstep m (by omega)
          have h3 := hge m (by omega)
          omega
    have hstrict : ∀ k l, k < l → l ≤ d → t k < t l := by
      intro k l hkl hld
      have h1 := hmono (l - 1) (by omega) k (by omega)
      have h2 := hstep (l - 1) (by omega)
      have h3 : l - 1 + 1 = l := by omega
      rw [h3] at h2
      omega
    have hdtd : d ≤ t d := hge d le_rfl
    -- a base of size `t d - d` together with `d` atoms outside it
    have hbase : (t d - d) + d ≤ (Finset.univ : Finset α).card := by
      rw [Finset.card_univ]; omega
    obtain ⟨s, f, hfinj, hfs, hscard, -, -⟩ := exists_base_and_atoms hbase
    -- enumerate the base
    have hcardsub : Fintype.card {x // x ∈ s} = t d - d := by
      rw [Fintype.card_coe]; exact hscard
    let ee : {x // x ∈ s} ≃ Fin (t d - d) := Fintype.equivFinOfCardEq hcardsub
    let g : Fin (t d - d) → α := fun j => (ee.symm j : α)
    have hginj : Function.Injective g := by
      intro a b hab
      exact ee.symm.injective (Subtype.ext hab)
    have hgmem : ∀ j, g j ∈ s := fun j => (ee.symm j).2
    -- a nested family of pads inside the base, with `(P k).card = t k - k`
    obtain ⟨P, hPcard, hPsub, hPmono⟩ :
        ∃ P : ℕ → Finset α, (∀ k, k ≤ d → (P k).card = t k - k) ∧ (∀ k, P k ⊆ s) ∧
          (∀ k l, k ≤ l → l ≤ d → P k ⊆ P l) := by
      refine ⟨fun k => (Finset.univ : Finset (Fin (min (t k - k) (t d - d)))).image
          (fun j => g (Fin.castLE (min_le_right _ _) j)), ?_, ?_, ?_⟩
      · intro k hk
        have huniv : (Finset.univ : Finset (Fin (min (t k - k) (t d - d)))).card = t k - k := by
          simp [min_eq_left (hpad d le_rfl k hk)]
        rw [← huniv]
        apply Finset.card_image_of_injective
        intro a b hab
        exact Fin.castLE_injective _ (hginj hab)
      · intro k a ha
        simp only [Finset.mem_image] at ha
        obtain ⟨j, -, rfl⟩ := ha
        exact hgmem _
      · intro k l hkl hld a ha
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha ⊢
        obtain ⟨j, rfl⟩ := ha
        have hle : min (t k - k) (t d - d) ≤ min (t l - l) (t d - d) :=
          min_le_min (hpad l hld k hkl) le_rfl
        exact ⟨Fin.castLE hle j, congrArg g (Fin.ext rfl)⟩
    -- the copy: the atoms of `X`, padded up to the right size
    have hcardle : ∀ X : BoolLat d, X.card ≤ d := by
      intro X
      simpa using Finset.card_le_card (Finset.subset_univ X)
    have hdisj : ∀ (X : BoolLat d) (k : ℕ), Disjoint (X.image f) (P k) := by
      intro X k
      rw [Finset.disjoint_left]
      intro a haX haP
      simp only [Finset.mem_image] at haX
      obtain ⟨i, -, rfl⟩ := haX
      exact hfs i (hPsub k haP)
    have hcard : ∀ X : BoolLat d, (X.image f ∪ P X.card).card = t X.card := by
      intro X
      rw [Finset.card_union_of_disjoint (hdisj X X.card),
        Finset.card_image_of_injective _ hfinj, hPcard X.card (hcardle X)]
      have := hge X.card (hcardle X)
      omega
    have hmemf : ∀ (X : BoolLat d) (i : Fin d), f i ∈ X.image f ∪ P X.card ↔ i ∈ X := by
      intro X i
      constructor
      · intro hi
        rcases Finset.mem_union.mp hi with h1 | h2
        · obtain ⟨i', hi', he⟩ := Finset.mem_image.mp h1
          rwa [hfinj he] at hi'
        · exact absurd (hPsub _ h2) (hfs i)
      · intro hi
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem f hi)
    refine ⟨fun X => X.image f ∪ P X.card, ⟨?_, ?_⟩, hcard⟩
    · -- injective
      intro X Y hXY
      have hXY' : X.image f ∪ P X.card = Y.image f ∪ P Y.card := hXY
      ext i
      constructor
      · intro hi
        have hm := (hmemf X i).mpr hi
        rw [hXY'] at hm
        exact (hmemf Y i).mp hm
      · intro hi
        have hm := (hmemf Y i).mpr hi
        rw [← hXY'] at hm
        exact (hmemf X i).mp hm
    · -- strict inclusion of images exactly for strict inclusion of index sets
      intro X Y
      constructor
      · intro hss
        have hsub : X ⊆ Y := by
          intro i hi
          rw [← hmemf Y i]
          exact hss.1 ((hmemf X i).mpr hi)
        have hne : X ≠ Y := by
          rintro rfl
          exact (ssubset_irrefl _) hss
        exact lt_of_le_of_ne hsub hne
      · intro hlt
        have hsub : X ⊆ Y := le_of_lt hlt
        have hcardlt : X.card < Y.card := Finset.card_lt_card hlt
        have hsub2 : X.image f ∪ P X.card ⊆ Y.image f ∪ P Y.card := by
          apply Finset.union_subset
          · exact (Finset.image_subset_image hsub).trans Finset.subset_union_left
          · exact (hPmono X.card Y.card (le_of_lt hcardlt) (hcardle Y)).trans
              Finset.subset_union_right
        have hlt2 : (X.image f ∪ P X.card).card < (Y.image f ∪ P Y.card).card := by
          have e1 := hcard X
          have e2 := hcard Y
          have e3 := hstrict X.card Y.card hcardlt (hcardle Y)
          omega
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub2, ?_⟩
        intro heq
        have heq' : X.image f ∪ P X.card = Y.image f ∪ P Y.card := heq
        rw [heq'] at hlt2
        omega
  -- pick `d + 1` admissible levels out of `S`
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hS
  have hTS : ∀ n ∈ T, n ∈ S ∧ n ≤ Fintype.card α := by
    intro n hn
    have := hTsub hn
    rw [Finset.mem_filter] at this
    exact this
  let e : Fin (d + 1) ≃o {x // x ∈ T} := T.orderIsoOfFin hTcard
  let t : ℕ → ℕ := fun k => ((e ⟨min k d, by omega⟩ : {x // x ∈ T}) : ℕ)
  have htmem : ∀ k, t k ∈ T := fun k => (e ⟨min k d, by omega⟩).2
  have hstep : ∀ k < d, t k < t (k + 1) := by
    intro k hk
    have hlt : (⟨min k d, by omega⟩ : Fin (d + 1)) < ⟨min (k + 1) d, by omega⟩ := by
      rw [Fin.lt_def]
      simp only []
      omega
    exact e.strictMono hlt
  have hlast : t d ≤ Fintype.card α := (hTS _ (htmem d)).2
  obtain ⟨ι, hstrong, hcard⟩ := main t hstep hlast
  refine ⟨ι, hstrong, ?_⟩
  intro X
  have hm : (ι X).card ∈ S := by
    rw [hcard X]
    exact (hTS _ (htmem X.card)).1
  simpa [levelFamily] using hm
