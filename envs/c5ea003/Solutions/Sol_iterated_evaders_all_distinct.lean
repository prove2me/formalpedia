-- Prove2me | solution 1 for iterated_evaders_all_distinct
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T04:24:55.504044+00:00
-- url     : https://prove2.me/submissions/d083f1d8-84d7-43fa-b1a1-a297400cab73

-- Sol generated from EML/GameTheory/RepulsorTheory.lean
import Mathlib
import Definitions.Def_EML_GameTheory_RepulsorTheory

/-! # CatalogBuild.Physics.Classical.RepulsorTheory

Auto-generated from theorem catalog database.
Domain: Physics/Classical
Declarations: 33
-/

noncomputable section



































theorem solution(enum : ℕ → (ℕ → ℕ)) :
    ∀ i j, i ≠ j → iterated_evader i enum ≠ iterated_evader j enum := by
  intros i j hij h_eq; contrapose! hij; (
  have h_diff : ∀ n, iterated_evader (n + 1) enum 0 ≠ iterated_evader n enum 0 := by
    intro n
    simp [iterated_evader];
    exact Nat.succ_ne_self _;
  -- By induction on $n$, we can show that $iterated\_evader n enum 0$ is strictly increasing.
  have h_inc : StrictMono (fun n => iterated_evader n enum 0) := by
    refine' strictMono_nat_of_lt_succ fun n => _;
    induction' n with n ih <;> simp_all +decide [ iterated_evader ];
    · exact Nat.lt_succ_self _;
    · exact Nat.succ_lt_succ ih;
  exact h_inc.injective ( congr_fun h_eq 0 ))
