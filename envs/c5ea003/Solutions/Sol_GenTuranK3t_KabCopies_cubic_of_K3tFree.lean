-- Prove2me | solution 1 for GenTuranK3t.KabCopies_cubic_of_K3tFree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:20:46.643509+00:00
-- url     : https://prove2.me/submissions/b517d1ab-fcb1-4ebe-9cae-d26123697e64

-- Sol generated from Probability/GenTuranK3tUpperBound.lean
import Mathlib
import Definitions.Def_Probability_GenTuranK3tUpperBound
import Theorems.Thm_GenTuranK3t_mem_cnbhd
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A cubic upper bound for the generalized Turán problem `ex(n, K_{a,b}, K_{3,t})`

For a host graph `G` on `n` vertices which contains no complete bipartite subgraph
`K_{3,t}` — equivalently, in which every three vertices have at most `t - 1` common
neighbours — the number of copies of `K_{a,b}` (`a, b ≥ 3`) is `O(n³)`, with an explicit
constant depending only on `a`, `b` and `t`:

`#K_{a,b}-copies ≤ C(t-1, b) · C(t-1, a-3) · n³`.

The proof is a two-step fibred double count.  A copy is a pair `(A, B)` of vertex sets,
`|A| = a`, `|B| = b`, complete to each other.

* Choose three vertices `T ⊆ A`.  There are at most `C(n,3) ≤ n³` possibilities.
* Since every vertex of `B` is a common neighbour of `T`, `B` is a `b`-subset of
  `cnbhd G T`, a set of size `≤ t - 1` by `K_{3,t}`-freeness: `≤ C(t-1, b)` possibilities.
* Symmetrically, every vertex of `A \ T` is a common neighbour of `B`, and `B` itself
  contains a triple, so `cnbhd G B` also has size `≤ t - 1`: `≤ C(t-1, a-3)` possibilities.

The bound follows because a copy is reconstructed from `(T, B, A \ T)`.

The downward closure of this bound under the subgraph order is
`Probability.GenTuranK3tDownwardClosure`.
-/

open Finset

open GenTuranK3t

variable {V : Type*} [Fintype V] [DecidableEq V]



/-- Common neighbourhoods shrink as the set grows. -/
lemma cnbhd_subset_of_subset {G : SimpleGraph V} [DecidableRel G.Adj] {S S' : Finset V}
    (h : S' ⊆ S) : cnbhd G S ⊆ cnbhd G S' := by
  intro w hw
  simp only [mem_cnbhd] at *
  exact fun u hu => hw u (h hu)



@[simp] lemma mem_KabCopies {G : SimpleGraph V} [DecidableRel G.Adj] {a b : ℕ}
    {P : Finset V × Finset V} :
    P ∈ KabCopies G a b ↔
      P.1.card = a ∧ P.2.card = b ∧ ∀ u ∈ P.1, ∀ v ∈ P.2, G.Adj u v := by
  simp [KabCopies]


lemma triple_subset {A : Finset V} (h : 3 ≤ A.card) : triple A ⊆ A := by
  rw [triple, dif_pos h]
  exact (Finset.exists_subset_card_eq h).choose_spec.1

lemma card_triple {A : Finset V} (h : 3 ≤ A.card) : (triple A).card = 3 := by
  rw [triple, dif_pos h]
  exact (Finset.exists_subset_card_eq h).choose_spec.2

/-- In a `K_{3,t}`-free graph, any vertex set with at least three elements has at most
`t - 1` common neighbours. -/
lemma card_cnbhd_le {G : SimpleGraph V} [DecidableRel G.Adj] {t : ℕ} (hfree : K3tFree G t)
    {S : Finset V} (hS : 3 ≤ S.card) : (cnbhd G S).card ≤ t - 1 := by
  obtain ⟨T, hTS, hT3⟩ := Finset.exists_subset_card_eq hS
  have hlt : (cnbhd G T).card < t := hfree T hT3
  have hle : (cnbhd G S).card ≤ (cnbhd G T).card :=
    Finset.card_le_card (cnbhd_subset_of_subset hTS)
  omega



open GenTuranK3t in
theorem solution(G : SimpleGraph V) [DecidableRel G.Adj] {a b t : ℕ}
    (ha : 3 ≤ a) (hb : 3 ≤ b) (_hbt : b + 1 ≤ t) (hfree : K3tFree G t) :
    (KabCopies G a b).card
      ≤ ((t - 1).choose b * (t - 1).choose (a - 3)) * (Fintype.card V) ^ 3 := by
  classical
  -- Step 1: fibre the copies over the chosen triple `T ⊆ A`.
  have hmaps : ∀ P ∈ KabCopies G a b,
      triple P.1 ∈ Finset.powersetCard 3 (univ : Finset V) := by
    intro P hP
    rw [mem_KabCopies] at hP
    have h3 : 3 ≤ P.1.card := hP.1 ▸ ha
    simp [Finset.mem_powersetCard, card_triple h3]
  have hfibre : ∀ T ∈ Finset.powersetCard 3 (univ : Finset V),
      ({P ∈ KabCopies G a b | triple P.1 = T}).card
        ≤ (t - 1).choose b * (t - 1).choose (a - 3) := by
    intro T _
    -- Step 2: inside a fibre, fibre again over `B`.
    have hmaps2 : ∀ P ∈ ({P ∈ KabCopies G a b | triple P.1 = T}),
        P.2 ∈ Finset.powersetCard b (cnbhd G T) := by
      intro P hP
      simp only [Finset.mem_filter, mem_KabCopies] at hP
      obtain ⟨⟨hA, hB, hadj⟩, hT⟩ := hP
      have h3 : 3 ≤ P.1.card := hA ▸ ha
      rw [Finset.mem_powersetCard]
      refine ⟨fun v hv => ?_, hB⟩
      rw [mem_cnbhd]
      intro u hu
      exact hadj u (triple_subset h3 (hT ▸ hu)) v hv
    have hfibre2 : ∀ B ∈ Finset.powersetCard b (cnbhd G T),
        ({P ∈ ({P ∈ KabCopies G a b | triple P.1 = T}) | P.2 = B}).card
          ≤ (t - 1).choose (a - 3) := by
      intro B hB
      rw [Finset.mem_powersetCard] at hB
      have hBcard : 3 ≤ B.card := hB.2 ▸ hb
      -- inject `(A, B) ↦ A \ T`
      have hinj : ((({P ∈ ({P ∈ KabCopies G a b | triple P.1 = T}) | P.2 = B})).card)
          ≤ (Finset.powersetCard (a - 3) (cnbhd G B)).card := by
        refine Finset.card_le_card_of_injOn (fun P => P.1 \ T) ?_ ?_
        · intro P hP
          simp only [Finset.mem_coe, Finset.mem_filter, mem_KabCopies] at hP
          obtain ⟨⟨⟨hA, hBc, hadj⟩, hT⟩, hPB⟩ := hP
          have h3 : 3 ≤ P.1.card := hA ▸ ha
          have hTA : T ⊆ P.1 := hT ▸ triple_subset h3
          rw [Finset.mem_coe, Finset.mem_powersetCard]
          constructor
          · intro u hu
            rw [Finset.mem_sdiff] at hu
            rw [mem_cnbhd]
            intro v hv
            exact (hadj u hu.1 v (hPB ▸ hv)).symm
          · have hTcard : T.card = 3 := hT ▸ card_triple h3
            rw [Finset.card_sdiff_of_subset hTA, hA, hTcard]
        · intro P hP Q hQ hPQ
          simp only [Finset.mem_coe, Finset.mem_filter, mem_KabCopies] at hP hQ
          obtain ⟨⟨⟨hA, _, _⟩, hT⟩, hPB⟩ := hP
          obtain ⟨⟨⟨hA', _, _⟩, hT'⟩, hQB⟩ := hQ
          have h3 : 3 ≤ P.1.card := hA ▸ ha
          have h3' : 3 ≤ Q.1.card := hA' ▸ ha
          have hTP : T ⊆ P.1 := hT ▸ triple_subset h3
          have hTQ : T ⊆ Q.1 := hT' ▸ triple_subset h3'
          have h1 : P.1 = Q.1 := by
            have := congrArg (fun s => T ∪ s) hPQ
            simpa [Finset.union_sdiff_of_subset hTP, Finset.union_sdiff_of_subset hTQ] using this
          exact Prod.ext h1 (by rw [hPB, hQB])
      calc ((({P ∈ ({P ∈ KabCopies G a b | triple P.1 = T}) | P.2 = B})).card)
          ≤ (Finset.powersetCard (a - 3) (cnbhd G B)).card := hinj
        _ = ((cnbhd G B).card).choose (a - 3) := Finset.card_powersetCard _ _
        _ ≤ (t - 1).choose (a - 3) :=
            Nat.choose_le_choose _ (card_cnbhd_le hfree hBcard)
    have hstep := Finset.card_le_mul_card_image_of_maps_to hmaps2 _ hfibre2
    have hpow : (Finset.powersetCard b (cnbhd G T)).card ≤ (t - 1).choose b := by
      rw [Finset.card_powersetCard]
      exact Nat.choose_le_choose _ (card_cnbhd_le hfree (by
        rcases Finset.mem_powersetCard.mp ‹T ∈ Finset.powersetCard 3 (univ : Finset V)› with ⟨-, hT3⟩
        omega))
    calc ({P ∈ KabCopies G a b | triple P.1 = T}).card
        ≤ (t - 1).choose (a - 3) * (Finset.powersetCard b (cnbhd G T)).card := hstep
      _ ≤ (t - 1).choose (a - 3) * (t - 1).choose b := Nat.mul_le_mul_left _ hpow
      _ = (t - 1).choose b * (t - 1).choose (a - 3) := Nat.mul_comm _ _
  have hmain := Finset.card_le_mul_card_image_of_maps_to hmaps _ hfibre
  have hcard : (Finset.powersetCard 3 (univ : Finset V)).card ≤ (Fintype.card V) ^ 3 := by
    rw [Finset.card_powersetCard, Finset.card_univ]
    exact Nat.choose_le_pow _ _
  exact hmain.trans (Nat.mul_le_mul_left _ hcard)
