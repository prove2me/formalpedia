-- Prove2me | solution 1 for SubsetSpectrum.spec_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:30:58.049369+00:00
-- url     : https://prove2.me/submissions/ae641ff5-74dd-4dbb-b01c-a2386beaf8fd

-- Sol generated from Applications/ActionSpectrum/Shadow.lean
import Mathlib
import Definitions.Def_Applications_ActionSpectrum_Basic
import Definitions.Def_Applications_ActionSpectrum_Shadow
import Theorems.Thm_SubsetSpectrum_card_of_mem_orb
import Theorems.Thm_SubsetSpectrum_mem_orb_self
import Theorems.Thm_SubsetSpectrum_orb_eq_of_mem

/-!
# Shadow inequalities for the subset spectrum, and a group-free log-concavity guard

The guarded log-concavity bound of `Applications.ActionSpectrum.LogConcavity`
(`t_{r-1}·t_{r+1} ≤ |G|²·t_r²`) degrades badly for large groups.  Here we prove a bound
which does **not** mention `|G|` at all, by a shadow (deletion/extension) argument on
orbits:

* `SubsetSpectrum.spec_succ_le` : `t_{r+1} ≤ (n - r) · t_r`;
* `SubsetSpectrum.spec_le_mul_spec_succ` : `t_r ≤ (r + 1) · t_{r+1}` (by complementation);
* `SubsetSpectrum.spec_mul_spec_le_shadow_bound` : `t_{r-1} · t_{r+1} ≤ r·(n-r) · t_r²`.

The last inequality is the *sharp shape* of the failed conjecture: the spectrum of any
finite action is log-concave up to the factor `r(n-r)`, which is exactly the failure ratio
of the binomial recursion at the boundary.  For the counterexample `C₄` on `4` points at
`r = 1` it reads `t_0·t_2 = 2 ≤ 1·3·1 = 3`.

The engine is:

> every orbit of `(r+1)`-sets is obtained from a *fixed representative* `s` of some orbit of
> `r`-sets by adding one of the `n - r` points outside `s`.
-/

open Finset

open SubsetSpectrum

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X] [Fintype G] [Fintype X]

omit [Fintype G] [Fintype X] in
lemma act_subset {g : G} {s u : Finset X} (h : s ⊆ u) : act g s ⊆ act g u :=
  Finset.image_subset_image h

omit [Fintype X] in
lemma mem_orb_iff {s t : Finset X} : t ∈ orb G s ↔ ∃ g : G, act g s = t := by
  simp [orb]


omit [DecidableEq X] [Fintype X] in
lemma rep_mem {O : Finset (Finset X)} (h : O.Nonempty) : rep O ∈ O := by
  rw [rep, dif_pos h]
  exact h.choose_spec





open SubsetSpectrum in
theorem solution(r : ℕ) :
    spec G X (r + 1) ≤ (Fintype.card X - r) * spec G X r := by
  classical
  set B := ((univ : Finset X).powersetCard r).image (orb G) with hB
  set A := ((univ : Finset X).powersetCard (r + 1)).image (orb G) with hA
  -- the representative of an orbit in `B` is an `r`-set of that orbit
  have hrepB : ∀ O ∈ B, rep O ∈ O ∧ (rep O).card = r := by
    intro O hO
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hO
    have hne : (orb G s).Nonempty := ⟨s, mem_orb_self s⟩
    have hmem := rep_mem hne
    exact ⟨hmem, by rw [card_of_mem_orb hmem, (mem_powersetCard.1 hs).2]⟩
  -- the covering
  have hcov : A ⊆ B.biUnion (fun O => ((rep O)ᶜ).image (fun x => orb G (insert x (rep O)))) := by
    intro P hP
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hP
    have hucard : u.card = r + 1 := (mem_powersetCard.1 hu).2
    obtain ⟨s, hsu, hscard⟩ : ∃ s ⊆ u, s.card = r :=
      Finset.exists_subset_card_eq (by omega)
    have hsB : orb G s ∈ B := Finset.mem_image_of_mem _ (mem_powersetCard.2 ⟨subset_univ _, hscard⟩)
    obtain ⟨hmem, hcard⟩ := hrepB _ hsB
    -- move `s` onto the representative
    obtain ⟨g, hg⟩ := mem_orb_iff.1 hmem
    have hsub : rep (orb G s) ⊆ act g u := by rw [← hg]; exact act_subset hsu
    have hvcard : (act g u).card = r + 1 := by rw [act_card, hucard]
    have hssub : rep (orb G s) ⊂ act g u := by
      refine Finset.ssubset_iff_of_subset hsub |>.2 ?_
      by_contra hcon
      push_neg at hcon
      have : act g u ⊆ rep (orb G s) := fun x hx => by
        by_contra hx'
        exact hx' (hcon x hx)
      have := Finset.card_le_card this
      omega
    obtain ⟨x, hxv, hxs⟩ := Finset.exists_of_ssubset hssub
    have hins : insert x (rep (orb G s)) = act g u := by
      refine Finset.eq_of_subset_of_card_le (Finset.insert_subset hxv hsub) ?_
      rw [hvcard, Finset.card_insert_of_notMem hxs, hcard]
    refine Finset.mem_biUnion.2 ⟨orb G s, hsB, ?_⟩
    refine Finset.mem_image.2 ⟨x, Finset.mem_compl.2 hxs, ?_⟩
    rw [hins]
    exact orb_eq_of_mem (mem_orb_iff.2 ⟨g, rfl⟩)
  -- count
  have hcard : A.card ≤ ∑ O ∈ B, (((rep O)ᶜ : Finset X).image
      (fun x => orb G (insert x (rep O)))).card :=
    le_trans (Finset.card_le_card hcov) Finset.card_biUnion_le
  have hbound : ∀ O ∈ B, (((rep O)ᶜ : Finset X).image
      (fun x => orb G (insert x (rep O)))).card ≤ Fintype.card X - r := by
    intro O hO
    obtain ⟨-, hcardO⟩ := hrepB O hO
    calc (((rep O)ᶜ : Finset X).image (fun x => orb G (insert x (rep O)))).card
        ≤ ((rep O)ᶜ : Finset X).card := Finset.card_image_le
      _ = Fintype.card X - r := by rw [Finset.card_compl, hcardO]
  calc spec G X (r + 1) = A.card := rfl
    _ ≤ ∑ O ∈ B, (((rep O)ᶜ : Finset X).image (fun x => orb G (insert x (rep O)))).card := hcard
    _ ≤ ∑ _O ∈ B, (Fintype.card X - r) := Finset.sum_le_sum hbound
    _ = (Fintype.card X - r) * spec G X r := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
        rfl
