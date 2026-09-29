-- Prove2me | solution 1 for RamseyTheory.arrows_step
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:04:34.407553+00:00
-- url     : https://prove2.me/submissions/8b535bb3-e062-4676-a8b3-951b6d052a27

-- Sol generated from Applications/Combinatorics/Ramsey.lean
import Mathlib
import Definitions.Def_Applications_Combinatorics_Ramsey
/-
# Finite two‑colour Ramsey theory

This file develops the elementary theory of finite two‑colour Ramsey numbers,
culminating in the exact value `R(3,3) = 6` and the Erdős–Szekeres binomial
upper bound `R(s+1, t+1) ≤ C(s+t, s)`.

A *two‑colouring* of a complete graph is encoded by a single `SimpleGraph G`:
the edges of `G` are the **red** edges and the edges of its complement `Gᶜ`
are the **blue** edges.  A red clique is then a clique of `G` and a blue clique
is a clique of `Gᶜ`.

The central relation is the *arrow* relation `Arrows n s t`
(classically written `n → (s, t)`): every red/blue colouring of any vertex set
of size at least `n` contains a red `s`‑clique or a blue `t`‑clique.
-/


open scoped Classical
open SimpleGraph Finset

open RamseyTheory

/-! ## Core combinatorial objects -/



/-! ## Monotonicity -/


/-! ## The Erdős–Szekeres recursion -/






/-! ## The value `R(3,3) = 6` -/









open RamseyTheory in
theorem solution{m n s t : ℕ} (hmpos : 0 < m) (hnpos : 0 < n)
    (hm : Arrows m s (t + 1)) (hn : Arrows n (s + 1) t) :
    Arrows (m + n) (s + 1) (t + 1) := by
  intro V hdec G W hcard
  obtain ⟨v, hv⟩ : ∃ v ∈ W, True := by
    exact Exists.elim ( Finset.card_pos.mp ( by linarith ) ) fun x hx => ⟨ x, hx, trivial ⟩;
  set R := (W.erase v).filter (fun x => G.Adj v x) with hR
  set B := (W.erase v).filter (fun x => ¬ G.Adj v x) with hB
  have hRcard : R.card + B.card = W.card - 1 := by
    rw [ Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv.1 ]
  have hRorB : m ≤ R.card ∨ n ≤ B.card := by
    omega;
  cases' hRorB with hRorB hRorB <;> [ have := hm G R hRorB; have := hn G B hRorB ] <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
  · obtain this | this := this;
    · obtain ⟨ S, hS₁, hS₂, hS₃ ⟩ := this; use Or.inl ⟨ Insert.insert v S, ?_, ?_, ?_ ⟩ <;> simp_all +decide [ Finset.subset_iff, SimpleGraph.isClique_iff ] ;
      rw [ Finset.card_insert_of_notMem ( fun h => by simpa [ h ] using hS₁ h ), hS₃ ];
    · exact Or.inr <| by obtain ⟨ S, hS₁, hS₂, hS₃ ⟩ := this; exact ⟨ S, Finset.Subset.trans hS₁ <| Finset.filter_subset _ _ |> Finset.Subset.trans <| Finset.erase_subset _ _, hS₂, hS₃ ⟩ ;
  · rcases this with ( ⟨ S, hS₁, hS₂, hS₃ ⟩ | ⟨ S, hS₁, hS₂, hS₃ ⟩ ) <;> simp_all +decide [ Finset.subset_iff ];
    · exact Or.inl ⟨ S, fun x hx => hS₁ hx |>.1 |>.2, hS₂, hS₃ ⟩;
    · refine Or.inr ⟨ Insert.insert v S, ?_, ?_, ?_ ⟩ <;> simp_all +decide [ SimpleGraph.isIndepSet_iff ];
      · simp_all +decide [ Set.Pairwise, SimpleGraph.adj_comm ];
      · rw [ Finset.card_insert_of_notMem ( fun h => by simpa [ h ] using hS₁ h ), hS₃ ]
