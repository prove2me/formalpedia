-- Prove2me | solution 1 for AlmostLossless.exists_scheme_successProb
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T14:12:17.926258+00:00
-- url     : https://prove2.me/submissions/4d9397d1-5c1b-42b4-bbba-fa980013bc07

import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Definitions.Def_Bridges_MinEntropy
open AlmostLossless NonArchInfoTheory in
theorem solution {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ} (μ : FinProbDist α)
    {H : Fin K → α → Fin M} (hU : Universal2 H) (hK : 0 < K) (hM : 0 < M)
    (l : List α) (hnd : l.Nodup) (δ : ℝ) (hδ : setMass μ (l.toFinset)ᶜ ≤ δ) :
    ∃ k : Fin K, 1 - (δ + (l.length : ℝ) / M) ≤ successProb μ (hashScheme l (H k)) := by
  have hsum : ∀ (S A : Finset α), (M : ℝ) * ∑ k : Fin K, setMass μ (A.filter (fun x => Collides H k S x))
      ≤ (K : ℝ) * S.card * setMass μ A := by
    intro S A
    unfold setMass
    have hswap : ∑ k : Fin K, ∑ x ∈ A.filter (fun x => Collides H k S x), μ.mass x
        = ∑ x ∈ A, μ.mass x * ((Finset.univ.filter (fun k => Collides H k S x)).card : ℝ) := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      split_ifs <;> simp
    have hkeys : ∀ x, ((Finset.univ.filter (fun k => Collides H k S x)).card : ℝ) * M
        ≤ S.card * K := by
      intro x
      have hsub : Finset.univ.filter (fun k => Collides H k S x)
          ⊆ (S.erase x).biUnion (fun y => Finset.univ.filter (fun k => H k y = H k x)) := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Collides, collisionSet,
          Finset.Nonempty] at hk
        obtain ⟨y, hy⟩ := hk
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨y, hy.1, hy.2⟩
      have h1 : ((Finset.univ.filter (fun k => Collides H k S x)).card : ℝ)
          ≤ ∑ y ∈ S.erase x, ((Finset.univ.filter (fun k => H k y = H k x)).card : ℝ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      have h2 : ∀ y ∈ S.erase x, ((Finset.univ.filter (fun k => H k y = H k x)).card : ℝ) * M ≤ K :=
        fun y hy => hU y x (Finset.ne_of_mem_erase hy)
      have hce : ((S.erase x).card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_erase_le
      calc ((Finset.univ.filter (fun k => Collides H k S x)).card : ℝ) * M
          ≤ (∑ y ∈ S.erase x, ((Finset.univ.filter (fun k => H k y = H k x)).card : ℝ)) * M :=
            mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
        _ = ∑ y ∈ S.erase x, ((Finset.univ.filter (fun k => H k y = H k x)).card : ℝ) * M :=
            Finset.sum_mul _ _ _
        _ ≤ ∑ _y ∈ S.erase x, (K : ℝ) := Finset.sum_le_sum h2
        _ = ((S.erase x).card : ℝ) * K := by simp
        _ ≤ S.card * K := mul_le_mul_of_nonneg_right hce (Nat.cast_nonneg _)
    rw [hswap, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum (fun x _ => ?_)
    have hk := hkeys x
    have hμ := μ.mass_nonneg x
    nlinarith [mul_le_mul_of_nonneg_left hk hμ]
  have hscan : ∀ (h : α → Fin M) (i : Fin M) (l : List α),
      (scanCost h i l).1 = l.filter (fun y => decide (h y = i)) := by
    intro h i l
    induction l with
    | nil => rfl
    | cons a t ih =>
      simp only [scanCost, List.filter_cons, ih]
      split_ifs <;> simp_all
  have hfs : ∀ (h : α → Fin M) (x : α) (l : List α), l.Nodup → x ∈ l → (∀ y ∈ l, h y = h x → y = x) →
      l.filter (fun z => decide (h z = h x)) = [x] := by
    intro h x l hnd hx huniq
    induction l with
    | nil => simp at hx
    | cons a t ih =>
      rw [List.nodup_cons] at hnd
      by_cases hax : a = x
      · subst hax
        have hnil : t.filter (fun z => decide (h z = h a)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro y hy hyh
          have := huniq y (List.mem_cons_of_mem _ hy) (by simpa using hyh)
          exact hnd.1 (this ▸ hy)
        simp [hnil]
      · have hxt : x ∈ t := by
          rcases List.mem_cons.mp hx with h1 | h1
          · exact absurd h1.symm hax
          · exact h1
        have hha : h a ≠ h x := fun hh => hax (huniq a (List.mem_cons_self) hh)
        rw [List.filter_cons, if_neg (by simpa using hha)]
        exact ih hnd.2 hxt (fun y hy hyh => huniq y (List.mem_cons_of_mem _ hy) hyh)
  have hsucc : ∀ (h : α → Fin M) (x : α), x ∈ l → (¬ ∃ y ∈ l.toFinset, y ≠ x ∧ h y = h x) →
      (hashScheme l h).dec ((hashScheme l h).enc x) = some x := by
    intro h x hx hnc
    have huniq : ∀ y ∈ l, h y = h x → y = x := by
      intro y hy hyh
      by_contra hne
      exact hnc ⟨y, List.mem_toFinset.mpr hy, hne, hyh⟩
    show decodeList h l (h x) = some x
    unfold decodeList
    rw [hscan, hfs h x l hnd hx huniq]
  set S := l.toFinset with hSdef
  obtain ⟨k, hk⟩ : ∃ k : Fin K,
      (M : ℝ) * setMass μ (S.filter (fun x => Collides H k S x)) ≤ (S.card : ℝ) * setMass μ S := by
    by_contra hall
    push Not at hall
    have hlt : ∑ _k : Fin K, (S.card : ℝ) * setMass μ S
        < ∑ k : Fin K, (M : ℝ) * setMass μ (S.filter (fun x => Collides H k S x)) :=
      Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hK⟩⟩) (fun k _ => hall k)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hlt
    have := hsum S S
    nlinarith
  refine ⟨k, ?_⟩
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hScard : (S.card : ℝ) = l.length := by
    rw [hSdef, List.toFinset_card_of_nodup hnd]
  have htot : setMass μ S + setMass μ Sᶜ = 1 := by
    unfold setMass
    rw [Finset.sum_add_sum_compl]
    exact μ.mass_sum_one
  have hS1 : setMass μ S ≤ 1 := by
    have : 0 ≤ setMass μ Sᶜ := Finset.sum_nonneg (fun x _ => μ.mass_nonneg x)
    linarith
  have hcollM : setMass μ (S.filter (fun x => Collides H k S x)) ≤ (l.length : ℝ) / M := by
    rw [le_div_iff₀ hMpos, ← hScard]
    have h0 : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hsplit : setMass μ (S.filter (fun x => Collides H k S x))
      + setMass μ (S.filter (fun x => ¬ Collides H k S x)) = setMass μ S := by
    unfold setMass
    exact Finset.sum_filter_add_sum_filter_not S _ _
  have hgood : setMass μ (S.filter (fun x => ¬ Collides H k S x))
      ≤ successProb μ (hashScheme l (H k)) := by
    unfold successProb setMass
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      rw [Finset.mem_filter] at hx
      have hxl : x ∈ l := List.mem_toFinset.mp hx.1
      have hnc : ¬ ∃ y ∈ l.toFinset, y ≠ x ∧ H k y = H k x := by
        rintro ⟨y, hy, hne, hyh⟩
        apply hx.2
        simp only [Collides, collisionSet, Finset.Nonempty]
        exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, hy⟩, hyh⟩⟩
      simp only [successSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hsucc (H k) x hxl hnc
    · intro x _ _
      exact μ.mass_nonneg x
  linarith
