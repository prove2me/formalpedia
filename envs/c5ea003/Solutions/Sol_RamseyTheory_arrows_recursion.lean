-- Prove2me | solution 1 for RamseyTheory.arrows_recursion
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:07:08.461833+00:00
-- url     : https://prove2.me/submissions/08d00f6d-084e-45b0-b05e-5cbc6fb8cd5f

-- Sol generated from Applications/Combinatorics/Ramsey.lean
import Mathlib
import Definitions.Def_Applications_Combinatorics_Ramsey
import Theorems.Thm_RamseyTheory_arrows_step
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


/-- A single vertex is a red `1`-clique, so `1 → (1, b)` for every `b`. -/
theorem arrows_one_red (b : ℕ) : Arrows 1 1 b := by
  intro V _ G W hW
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < W.card)
  exact Or.inl ⟨{v}, by simpa using hv, ⟨by simp [SimpleGraph.isClique_iff], by simp⟩⟩

/-- A single vertex is a blue `1`-clique, so `1 → (a, 1)` for every `a`. -/
theorem arrows_one_blue (a : ℕ) : Arrows 1 a 1 := by
  intro V _ G W hW
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < W.card)
  exact Or.inr ⟨{v}, by simpa using hv, ⟨by simp [SimpleGraph.isClique_iff], by simp⟩⟩



/-! ## The value `R(3,3) = 6` -/









open RamseyTheory in
theorem solution(s t : ℕ) : Arrows ((s + t).choose s) (s + 1) (t + 1) := by
  by_contra h_contra;
  revert s t;
  intro s;
  induction' s with s ih <;> simp_all +decide;
  · exact fun t => arrows_one_red _;
  · have arrows_inductive_step : ∀ t, Arrows ((s + 1 + t).choose (s + 1)) (s + 2) (t + 1) := by
      intro t
      induction' t with t ih
      ·
        norm_num +zetaDelta at *;
        exact arrows_one_blue _
      ·
        -- Apply the arrows_step lemma with the induction hypotheses.
        have h_step : Arrows ((s + (t + 1)).choose s + (s + 1 + t).choose (s + 1)) (s + 2) (t + 2) := by
          apply arrows_step;
          · exact Nat.choose_pos ( by linarith );
          · exact Nat.choose_pos ( by linarith );
          · solve_by_elim;
          · assumption;
        grind +suggestions;
    grind +revert
