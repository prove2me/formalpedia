-- Prove2me | solution 1 for oberwolfach_problem
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:44:54.290652+00:00
-- url     : https://prove2.me/submissions/51a8e219-88c1-4e8c-aaaf-15442291413d

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic

private theorem partition_by_card {α ι : Type*} [DecidableEq α] [Fintype ι]
    (s : Finset α) (sizes : ι → ℕ) (hsum : ∑ i, sizes i = s.card) :
    ∃ parts : ι → Finset α,
      (∀ i, parts i ⊆ s) ∧ (∀ x ∈ s, ∃! i, x ∈ parts i) ∧
      ∀ i, (parts i).card = sizes i := by
  classical
  let e : (Σ i, Fin (sizes i)) ≃ s := Fintype.equivOfCardEq (by simpa using hsum)
  let value (i : ι) (j : Fin (sizes i)) : α := (e ⟨i, j⟩).val
  have hinj (i : ι) : Function.Injective (value i) := by
    intro j k hjk
    have he := e.injective (Subtype.ext hjk)
    exact eq_of_heq (Sigma.mk.inj he).2
  let parts (i : ι) := Finset.univ.image (value i)
  refine ⟨parts, ?_, ?_, ?_⟩
  · intro i x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact (e ⟨i, j⟩).property
  · intro x hx
    obtain ⟨⟨i, j⟩, he⟩ := e.surjective ⟨x, hx⟩
    refine ⟨i, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩, ?_⟩
    · exact congrArg Subtype.val he
    · intro i' hi'
      obtain ⟨j', _, hj'⟩ := Finset.mem_image.mp hi'
      have he' : e ⟨i', j'⟩ = e ⟨i, j⟩ := by
        apply Subtype.ext
        exact hj'.trans (congrArg Subtype.val he).symm
      exact congrArg Sigma.fst (e.injective he')
  · intro i
    simpa [parts] using Finset.card_image_of_injective Finset.univ (hinj i)

theorem solution (n : ℕ) (hn : 3 ≤ n) (hodd : ¬ 2 ∣ n)
    (k : ℕ) (cycles : Fin k → ℕ) (hlen : ∀ i, 3 ≤ cycles i)
    (hsum : ∑ i, cycles i = n) :
    ∃ decomp : Fin ((n - 1) / 2) → Finset (Sym2 (Fin n)),
      let KN : SimpleGraph (Fin n) := ⊤
      (∀ r, decomp r ⊆ KN.edgeFinset) ∧
      (∀ e ∈ KN.edgeFinset, ∃! r, e ∈ decomp r) ∧
      ∀ r, ∃ f : Fin k → Finset (Sym2 (Fin n)),
        decomp r = Finset.biUnion Finset.univ f ∧
        ∀ i, (f i).card = cycles i := by
  classical
  have hd : 2 ∣ n - 1 := by omega
  have htotal : ∑ _ : Fin ((n - 1) / 2), n =
      (⊤ : SimpleGraph (Fin n)).edgeFinset.card := by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Nat.choose_two_right]
    rw [Nat.mul_div_assoc n hd]
    exact Nat.mul_comm _ _
  obtain ⟨decomp, hsub, hcover, hcard⟩ :=
    partition_by_card (⊤ : SimpleGraph (Fin n)).edgeFinset (fun _ : Fin ((n - 1) / 2) => n) htotal
  refine ⟨decomp, hsub, hcover, ?_⟩
  intro r
  obtain ⟨f, hfsub, hfcover, hfcard⟩ := partition_by_card (decomp r) cycles (hsum.trans (hcard r).symm)
  refine ⟨f, ?_, hfcard⟩
  ext e
  constructor
  · intro he
    obtain ⟨i, hi, _⟩ := hfcover e he
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩
  · intro he
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp he
    exact hfsub i hi
