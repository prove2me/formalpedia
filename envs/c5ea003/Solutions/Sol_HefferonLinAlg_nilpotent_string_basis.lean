-- Prove2me | solution 1 for HefferonLinAlg.nilpotent_string_basis
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-08-07T15:27:42.277945+00:00
-- url     : https://prove2.me/submissions/ffcc52cd-38ad-4217-9211-6b8f4de77db6

import Mathlib

open Module

universe u

/-- The vector family of the extended string basis: each old string gains a new top vector,
and each complementary kernel vector becomes a string of length one. -/
private def stringVec {V : Type u} {ι' τ : Type u} (sz' : ι' → ℕ) (top : ι' → V) (mid : ∀ i, Fin (sz' i) → V) (ext : τ → V) :
    (Σ i : ι' ⊕ τ, Fin (Sum.elim (fun i => sz' i + 1) (fun _ => 1) i)) → V
  | ⟨Sum.inl i, a⟩ =>
      if h : (a : ℕ) = 0 then top i else mid i ⟨(a : ℕ) - 1, by have := a.isLt; simp at this; omega⟩
  | ⟨Sum.inr s, _⟩ => ext s

private theorem stringVec_inl {V : Type u} {ι' τ : Type u} (sz' : ι' → ℕ) (top : ι' → V) (mid : ∀ i, Fin (sz' i) → V) (ext : τ → V)
    (i : ι') (a : Fin (sz' i + 1)) :
    stringVec sz' top mid ext ⟨Sum.inl i, a⟩ =
      if h : (a : ℕ) = 0 then top i
      else mid i ⟨(a : ℕ) - 1, by have := a.isLt; omega⟩ := rfl

private theorem stringVec_inr {V : Type u} {ι' τ : Type u} (sz' : ι' → ℕ) (top : ι' → V) (mid : ∀ i, Fin (sz' i) → V) (ext : τ → V)
    (s : τ) (a : Fin 1) :
    stringVec sz' top mid ext ⟨Sum.inr s, a⟩ = ext s := rfl

private theorem hasStringBasis_aux (K : Type*) [Field K] (n : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (f : Module.End K V), Module.finrank K V = n → IsNilpotent f →
    ∃ (ι : Type u) (_ : Fintype ι) (sz : ι → ℕ)
      (b : Module.Basis (Σ i : ι, Fin (sz i)) K V),
      (∀ i, 0 < sz i) ∧
        ∀ (i : ι) (a : Fin (sz i)),
          f (b ⟨i, a⟩) = if h : (a : ℕ) + 1 < sz i then b ⟨i, ⟨(a : ℕ) + 1, h⟩⟩ else 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ f hdim hnil
  classical
  by_cases hV : Module.finrank K V = 0
  · refine ⟨PEmpty.{u+1}, inferInstance, fun i => i.elim, ?_, fun i => i.elim, fun i => i.elim⟩
    refine Module.Basis.mk (v := fun p => p.1.elim) ?_ ?_
    · exact linearIndependent_empty_type
    · have : (⊤ : Submodule K V) = ⊥ := by
        rw [← Submodule.finrank_eq_zero (S := (⊤ : Submodule K V))]
        simpa using hV
      simp [this]
  have hWmaps : Set.MapsTo f ↑(LinearMap.range f) ↑(LinearMap.range f) := by
    intro x _
    exact LinearMap.mem_range_self f x
  set W := LinearMap.range f with hW
  set g : Module.End K W := f.restrict hWmaps with hg
  have hpow : ∀ (j : ℕ) (y : W), ((g ^ j) y : V) = ((f ^ j) (y : V)) := by
    intro j
    induction j with
    | zero => intro y; simp
    | succ j ihj =>
        intro y
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ihj (g y)]
        rfl
  have hgnil : IsNilpotent g := by
    obtain ⟨m, hm⟩ := hnil
    refine ⟨m, ?_⟩
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [hpow m x, hm]
    simp
  have hWlt : W ≠ ⊤ := by
    intro htop
    obtain ⟨m, hm⟩ := hnil
    have hr : ∀ j : ℕ, LinearMap.range (f ^ j) = ⊤ := by
      intro j
      induction j with
      | zero => simp [Module.End.one_eq_id]
      | succ j ihj =>
          rw [pow_succ, Module.End.mul_eq_comp, LinearMap.range_comp, ← hW, htop,
            Submodule.map_top]
          exact ihj
    have h0 := hr m
    rw [hm, LinearMap.range_zero] at h0
    apply hV
    rw [← finrank_top K V, ← h0, finrank_bot]
  have hWdim : Module.finrank K W < n := by
    rw [← hdim]
    exact Submodule.finrank_lt hWlt
  obtain ⟨ι', instι', sz', b', hpos', hstr'⟩ := ih _ hWdim g rfl hgnil
  letI : Fintype ι' := instι'
  -- preimages of the string tops
  have htops : ∀ i : ι', ∃ x : V, f x = ((b' ⟨i, ⟨0, hpos' i⟩⟩ : W) : V) := by
    intro i
    exact (b' ⟨i, ⟨0, hpos' i⟩⟩).2
  choose u hu using htops
  have hlast : ∀ i : ι', sz' i - 1 < sz' i := fun i => Nat.sub_lt (hpos' i) one_pos
  -- the middle vectors of the new strings are the old basis vectors
  set mid : ∀ i : ι', Fin (sz' i) → V := fun i c => ((b' ⟨i, c⟩ : W) : V) with hmid
  have hfmid : ∀ (i : ι') (c : Fin (sz' i)),
      f (mid i c) = if h : (c : ℕ) + 1 < sz' i then mid i ⟨(c : ℕ) + 1, h⟩ else 0 := by
    intro i c
    have h1 := hstr' i c
    have h2 : f (mid i c) = ((g (b' ⟨i, c⟩) : W) : V) := rfl
    rw [h1] at h2
    rw [h2]
    by_cases h : (c : ℕ) + 1 < sz' i
    · rw [dif_pos h, dif_pos h]
    · rw [dif_neg h, dif_neg h]
      simp
  have hfbot : ∀ i : ι', f (mid i ⟨sz' i - 1, hlast i⟩) = 0 := by
    intro i
    rw [hfmid i ⟨sz' i - 1, hlast i⟩, dif_neg]
    have := hpos' i
    simp
    omega
  set N := LinearMap.ker f with hN
  set Bot : ι' → N := fun i => ⟨mid i ⟨sz' i - 1, hlast i⟩, hfbot i⟩ with hBot
  have hBotLI : LinearIndependent K Bot := by
    apply LinearIndependent.of_comp N.subtype
    have h1 : LinearIndependent K (fun i : ι' => b' ⟨i, ⟨sz' i - 1, hlast i⟩⟩) :=
      b'.linearIndependent.comp
        (fun i : ι' => (⟨i, ⟨sz' i - 1, hlast i⟩⟩ : Σ i : ι', Fin (sz' i)))
        (fun p q hpq => by simpa using congrArg Sigma.fst hpq)
    exact h1.map' W.subtype (Submodule.ker_subtype W)
  set P : Submodule K N := Submodule.span K (Set.range Bot) with hP
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl P
  set τ := Module.Basis.ofVectorSpaceIndex K (C : Type u) with hτ
  set cB : Module.Basis τ K C := Module.Basis.ofVectorSpace K C with hcB
  letI : Fintype τ := FiniteDimensional.fintypeBasisIndex cB
  set ext : τ → V := fun s => (((cB s : C) : N) : V) with hext
  have hfext : ∀ s : τ, f (ext s) = 0 := by
    intro s
    exact ((cB s : C) : N).2
  set vv := stringVec sz' u mid ext with hvv
  have hfvv2 : ∀ (i : ι') (a : Fin (sz' i + 1)),
      f (vv ⟨Sum.inl i, a⟩) = if h : (a : ℕ) < sz' i then mid i ⟨(a : ℕ), h⟩ else 0 := by
    intro i a
    have ha := a.isLt
    have hp := hpos' i
    rw [hvv, stringVec_inl]
    by_cases h0 : (a : ℕ) = 0
    · rw [dif_pos h0, hu i, dif_pos (by omega)]
      exact congrArg (fun cc : Fin (sz' i) => ((b' ⟨i, cc⟩ : W) : V)) (Fin.ext (by simp [h0]))
    · rw [dif_neg h0, hfmid]
      by_cases h1 : (a : ℕ) - 1 + 1 < sz' i
      · rw [dif_pos h1, dif_pos (by omega)]
        exact congrArg (fun cc : Fin (sz' i) => ((b' ⟨i, cc⟩ : W) : V)) (Fin.ext (by simp; omega))
      · rw [dif_neg h1, dif_neg (by omega)]
  have hvvlast : ∀ i : ι', vv ⟨Sum.inl i, Fin.last (sz' i)⟩ = ((Bot i : N) : V) := by
    intro i
    rw [hvv, stringVec_inl, dif_neg (by simp; exact (hpos' i).ne')]
    rfl
  have hLI : LinearIndependent K vv := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have happ : ∑ p, c p • f (vv p) = 0 := by
      have h := congrArg (fun x => f x) hc
      simp only [map_sum, map_smul, map_zero] at h
      exact h
    rw [Fintype.sum_sigma, Fintype.sum_sum_type] at happ
    have hA : ∀ i : ι', ∑ a : Fin (sz' i + 1), c ⟨Sum.inl i, a⟩ • f (vv ⟨Sum.inl i, a⟩)
        = ∑ a : Fin (sz' i), c ⟨Sum.inl i, a.castSucc⟩ • mid i a := by
      intro i
      rw [Fin.sum_univ_castSucc]
      have hl : f (vv ⟨Sum.inl i, Fin.last (sz' i)⟩) = 0 := by
        rw [hfvv2, dif_neg]; simp
      rw [hl, smul_zero, add_zero]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [hfvv2, dif_pos (by simpa using a.isLt)]
      exact congrArg _ (congrArg (fun cc : Fin (sz' i) => mid i cc) (Fin.ext (by simp)))
    have hB : ∀ s : τ, ∑ a : Fin 1, c ⟨Sum.inr s, a⟩ • f (vv ⟨Sum.inr s, a⟩) = 0 := by
      intro s
      refine Finset.sum_eq_zero (fun a _ => ?_)
      rw [hvv, stringVec_inr, hfext, smul_zero]
    have happ2 : (∑ i : ι', ∑ a : Fin (sz' i + 1), c ⟨Sum.inl i, a⟩ • f (vv ⟨Sum.inl i, a⟩))
        + (∑ s : τ, ∑ a : Fin 1, c ⟨Sum.inr s, a⟩ • f (vv ⟨Sum.inr s, a⟩)) = 0 := happ
    simp only [hA, hB, Finset.sum_const_zero, add_zero] at happ2
    have hW0 : ∑ q : (Σ i : ι', Fin (sz' i)), c ⟨Sum.inl q.1, q.2.castSucc⟩ • b' q = 0 := by
      apply Submodule.injective_subtype W
      rw [map_sum, map_zero]
      simp only [map_smul, Submodule.subtype_apply]
      rw [Fintype.sum_sigma]
      exact happ2
    have hc1 : ∀ (i : ι') (a : Fin (sz' i)), c ⟨Sum.inl i, a.castSucc⟩ = 0 := by
      have h := (Fintype.linearIndependent_iff.mp b'.linearIndependent)
        (fun q => c ⟨Sum.inl q.1, q.2.castSucc⟩) hW0
      intro i a
      exact h ⟨i, a⟩
    rw [Fintype.sum_sigma, Fintype.sum_sum_type] at hc
    have hA2 : ∀ i : ι', ∑ a : Fin (sz' i + 1), c ⟨Sum.inl i, a⟩ • vv ⟨Sum.inl i, a⟩
        = c ⟨Sum.inl i, Fin.last (sz' i)⟩ • ((Bot i : N) : V) := by
      intro i
      rw [Fin.sum_univ_castSucc, hvvlast,
        Finset.sum_eq_zero (fun a _ => by rw [hc1 i a, zero_smul]), zero_add]
    have hB2 : ∀ s : τ, ∑ a : Fin 1, c ⟨Sum.inr s, a⟩ • vv ⟨Sum.inr s, a⟩
        = c ⟨Sum.inr s, (0 : Fin 1)⟩ • (((cB s : C) : N) : V) := by
      intro s
      rw [Fin.sum_univ_one, hvv, stringVec_inr, hext]
    have hc' : (∑ i : ι', ∑ a : Fin (sz' i + 1), c ⟨Sum.inl i, a⟩ • vv ⟨Sum.inl i, a⟩)
        + (∑ s : τ, ∑ a : Fin 1, c ⟨Sum.inr s, a⟩ • vv ⟨Sum.inr s, a⟩) = 0 := hc
    simp only [hA2, hB2] at hc'
    set x : N := ∑ i : ι', c ⟨Sum.inl i, Fin.last (sz' i)⟩ • Bot i with hx
    set y : C := ∑ s : τ, c ⟨Sum.inr s, (0 : Fin 1)⟩ • cB s with hy
    have hxy : x + (C.subtype y : N) = 0 := by
      apply Submodule.injective_subtype N
      rw [map_zero, map_add, hx, hy]
      simp only [map_sum, map_smul, Submodule.subtype_apply]
      exact hc'
    have hxP : x ∈ P := by
      rw [hx]
      exact Submodule.sum_mem _ (fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    have hzC : (C.subtype y : N) ∈ C := y.2
    have hx0 : x = 0 := by
      have hxC : x ∈ C := by
        have hxe : x = -(C.subtype y : N) := by
          rw [eq_neg_iff_add_eq_zero]; exact hxy
        rw [hxe]
        exact Submodule.neg_mem _ hzC
      exact (Submodule.disjoint_def.mp hC.disjoint) x hxP hxC
    have hy0 : y = 0 := by
      apply Submodule.injective_subtype C
      rw [map_zero]
      have := hxy
      rw [hx0, zero_add] at this
      exact this
    have hcLast : ∀ i : ι', c ⟨Sum.inl i, Fin.last (sz' i)⟩ = 0 :=
      (Fintype.linearIndependent_iff.mp hBotLI) _ (by rw [← hx]; exact hx0)
    have hcExt : ∀ (s : τ) (a : Fin 1), c ⟨Sum.inr s, a⟩ = 0 := by
      intro s a
      rw [Subsingleton.elim a (0 : Fin 1)]
      exact (Fintype.linearIndependent_iff.mp cB.linearIndependent) _
        (by rw [← hy]; exact hy0) s
    rintro ⟨(i | s), a⟩
    · refine Fin.lastCases ?_ ?_ a
      · exact hcLast i
      · intro d; exact hc1 i d
    · exact hcExt s a
  have hcard : Fintype.card
      (Σ i : ι' ⊕ τ, Fin (Sum.elim (fun i => sz' i + 1) (fun _ => 1) i))
      = Module.finrank K V := by
    have h1 : Module.finrank K (W : Type u) = ∑ i : ι', sz' i := by
      rw [Module.finrank_eq_card_basis b', Fintype.card_sigma]
      simp
    have h2 : Module.finrank K (N : Type u) = Fintype.card ι' + Fintype.card τ := by
      rw [← Submodule.finrank_add_eq_of_isCompl hC, hP, finrank_span_eq_card hBotLI,
        Module.finrank_eq_card_basis cB]
    have h3 := LinearMap.finrank_range_add_finrank_ker f
    rw [← hW, ← hN] at h3
    have hsum : (∑ _i : ι', Fintype.card (Fin (sz' _i + 1)))
        + (∑ _s : τ, Fintype.card (Fin 1)) = Module.finrank K V := by
      simp only [Fintype.card_fin]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
      omega
    rw [Fintype.card_sigma, Fintype.sum_sum_type]
    exact hsum
  refine ⟨ι' ⊕ τ, inferInstance, Sum.elim (fun i => sz' i + 1) (fun _ => 1),
    basisOfLinearIndependentOfCardEqFinrank' vv hLI hcard, ?_, ?_⟩
  · rintro (i | s) <;> simp [hpos']
  · rintro (i | s) a
    · rw [coe_basisOfLinearIndependentOfCardEqFinrank', hvv, stringVec_inl]
      by_cases h0 : (a : ℕ) = 0
      · rw [dif_pos h0, hu i, dif_pos (by simp; have := hpos' i; omega), stringVec_inl,
          dif_neg (by simp)]
        exact congrArg (fun c : Fin (sz' i) => ((b' ⟨i, c⟩ : W) : V)) (Fin.ext (by simp [h0]))
      · rw [dif_neg h0, hfmid]
        by_cases h1 : (a : ℕ) - 1 + 1 < sz' i
        · rw [dif_pos h1, dif_pos (by simp; omega), stringVec_inl, dif_neg (by simp)]
          exact congrArg (fun c : Fin (sz' i) => ((b' ⟨i, c⟩ : W) : V)) (Fin.ext (by simp; omega))
        · rw [dif_neg h1, dif_neg (by simp; omega)]
    · rw [coe_basisOfLinearIndependentOfCardEqFinrank', hvv, stringVec_inr, hfext,
        dif_neg (by simp)]

theorem solution {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) (hf : IsNilpotent f) :
    ∃ (k : ℕ) (sz : Fin k → ℕ) (b : Module.Basis (Σ i : Fin k, Fin (sz i)) K V),
      (∀ i, 0 < sz i) ∧
        ∀ (i : Fin k) (a : Fin (sz i)),
          f (b ⟨i, a⟩) =
            if h : (a : ℕ) + 1 < sz i then b ⟨i, ⟨(a : ℕ) + 1, h⟩⟩ else 0 := by
  classical
  obtain ⟨ι, instι, sz, b, hpos, hstr⟩ := hasStringBasis_aux K (Module.finrank K V) f rfl hf
  letI : Fintype ι := instι
  set e := Fintype.equivFin ι with he
  refine ⟨Fintype.card ι, fun j => sz (e.symm j), ?_⟩
  set E := Equiv.sigmaCongrLeft (β := fun i : ι => Fin (sz i)) e.symm with hE
  refine ⟨b.reindex E.symm, fun j => hpos _, ?_⟩
  intro j a
  rw [Module.Basis.reindex_apply, Equiv.symm_symm]
  have hEa : E ⟨j, a⟩ = ⟨e.symm j, a⟩ := rfl
  rw [hEa, hstr]
  by_cases h : (a : ℕ) + 1 < sz (e.symm j)
  · rw [dif_pos h, dif_pos h, Module.Basis.reindex_apply, Equiv.symm_symm]
    rfl
  · rw [dif_neg h, dif_neg h]
