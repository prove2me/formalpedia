-- Prove2me | solution 1 for Arexychen.Erdos180.isOLinear_extremalNumber_of_deleteIsolated_isAcyclic
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:25:45.142982+00:00
-- url     : https://prove2.me/submissions/0481250d-a9a1-498b-a0fa-4ceb1b33d9fc

import Definitions.Def_arexychen_erdos180_core
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic
import Theorems.Thm_Arexychen_Erdos180_edgeCount_le_of_isHFree_of_deleteIsolated_isAcyclic

namespace Arexychen


open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w



/-- A pointwise linear natural upper bound gives `O(n)`. -/
private theorem isOLinear_of_forall_le_mul
    (f : ℕ → ℕ) (C : ℕ) (hC : ∀ n, f n ≤ C * n) :
    IsOLinear f := by
  unfold IsOLinear
  refine IsBigO.of_bound (C : ℝ) (Filter.Eventually.of_forall ?_)
  intro n
  have hreal : (f n : ℝ) ≤ (C * n : ℕ) := by
    exact_mod_cast hC n
  simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hreal


















end Erdos180

end
end Arexychen

namespace Arexychen


open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w





/-- If every element of a set of natural numbers is at most `C`, then its
supremum is at most `C`.  This version also handles the empty set. -/
private theorem nat_sSup_le_of_forall_le {s : Set ℕ} {C : ℕ}
    (hC : ∀ m ∈ s, m ≤ C) :
    sSup s ≤ C := by
  classical
  rw [Nat.sSup_def ⟨C, hC⟩]
  exact Nat.find_min' ⟨C, hC⟩ hC








end Erdos180

end
end Arexychen

namespace Arexychen


open Filter
open Asymptotics

noncomputable section

namespace Erdos180

attribute [local instance] SimpleGraph.neighborSetFintype

universe u v

































-- `[Fintype α]` is unused in the statement but required by the proof
-- (the witness constant is `Fintype.card α`), hence the linter override.




-- `[Fintype α]` is unused in the statement but required by the proof
-- (it applies the guarded bound above), hence the linter override.
end Erdos180
end
end Arexychen

section
open Filter
open Asymptotics
attribute [local instance] SimpleGraph.neighborSetFintype
universe u v
open Arexychen.Erdos180 in
set_option linter.unusedFintypeInType false in
theorem solution
    {α : Type u} [Fintype α] (H : SimpleGraph α)
    (hforest : (deleteIsolated H).IsAcyclic) :
    IsOLinear (fun n => extremalNumber H n) := by
  classical
  rcases edgeCount_le_of_isHFree_of_deleteIsolated_isAcyclic H hforest with
    ⟨C, hC⟩
  refine isOLinear_of_forall_le_mul (fun n => extremalNumber H n) C ?_
  intro n
  unfold extremalNumber
  refine nat_sSup_le_of_forall_le ?_
  intro m hm
  rcases hm with ⟨G, hfree, rfl⟩
  letI : DecidableRel G.Adj := Classical.decRel _
  simpa using hC (Fin n) G hfree
end
namespace Arexychen
noncomputable section
namespace Erdos180


















end Erdos180

end
end Arexychen
