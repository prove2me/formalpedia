-- Prove2me | solution 1 for CondensationSemantics.compact_below_idealSup_mem
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:16:42.798696+00:00
-- url     : https://prove2.me/submissions/c92d5b31-09ac-4bd2-a1d6-e066e0839f73

-- Sol generated from Bridges/CondensationSemantics.lean
import Mathlib
import Definitions.Def_Bridges_CondensationSemantics
/-
# Condensation Semantics for Algebraic Fixed Points via Idempotent Galois Reconstruction

Bridge: connects algebraic lattice semantics (compact generation, ideals, nuclei, fixed points)
to EML / emergent computation semantics (iterative closure, convergence rank, certified termination)
and to cryptographic/ML/physics applications (post-quantum lattice protocols, neural certified
robustness, thermodynamic entropy stabilization, quantum condensation).
-/

set_option maxHeartbeats 800000

noncomputable section

open CondensationSemantics

/-! ## Core Structures -/












/-! ## Utility lemmas -/




/-! ## Monotonicity, Extensivity, Idempotence -/






/-! ## Iteration -/





/-! ## Termination -/



/-! ## Fixed Points ↔ Closed Ideals -/





/-! ## Witness Extraction and Robustness -/

/-
**Compact witness for non-closed states (∀ → ∃ alternation).**
-/



/-! ## Application Theorems -/












/-! ## Finite Lattice Specialization -/



/-! ## Examples -/



/-! ## Chain Bound -/





open CondensationSemantics in
theorem solution{P : Type*} [CompleteLattice P]
    (I : IdealCondensation P) {k : P} (hk : IsCompactElement k)
    (hk_le : k ≤ idealSup I) : k ∈ I.carrier := by
      have := hk;
      specialize this { y | ∃ x ∈ I.carrier, y ≤ x };
      contrapose! this;
      refine' ⟨ _, _, _, _, hk_le, _ ⟩;
      · exact ⟨ ⊥, ⟨ ⊥, I.bot_mem', bot_le ⟩ ⟩;
      · intro x hx y hy;
        obtain ⟨ a, ha, hx ⟩ := hx
        obtain ⟨ b, hb, hy ⟩ := hy
        use a ⊔ b;
        exact ⟨ ⟨ _, I.sup_mem' ha hb, le_rfl ⟩, le_trans hx ( le_sup_left ), le_trans hy ( le_sup_right ) ⟩;
      · refine' ⟨ fun y hy => _, fun y hy => _ ⟩;
        · exact le_trans hy.choose_spec.2 ( le_sSup hy.choose_spec.1 );
        · exact sSup_le fun x hx => hy ⟨ x, hx, le_rfl ⟩;
      · rintro x ⟨ y, hy, hxy ⟩ hky;
        exact this ( I.lower' hy ( le_trans hky hxy ) )
