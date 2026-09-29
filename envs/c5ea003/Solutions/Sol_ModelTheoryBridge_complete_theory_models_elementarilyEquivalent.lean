-- Prove2me | solution 1 for ModelTheoryBridge.complete_theory_models_elementarilyEquivalent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:08:35.306504+00:00
-- url     : https://prove2.me/submissions/a1bc9808-0fe3-4e4d-8ff4-7dce86bceea9

-- Sol generated from Bridges/AbstractAlgebra/ModelTheoryBridge.lean
import Mathlib
import Definitions.Def_Bridges_AbstractAlgebra_ModelTheoryBridge
/-
  Model Theory and Algebra Bridge
  ================================
  
  Formalizes fundamental results connecting model theory and algebra:
  
  1. Isomorphic structures are elementarily equivalent
  2. Models of a complete theory are elementarily equivalent  
  3. Complete theories are characterized by their models (T ⊨ φ ↔ M ⊨ φ)
  4. Elementary equivalence preserves the model relation
  5. κ-categoricity implies elementary equivalence of same-size models
  6. A theory is complete iff all models are elementarily equivalent
  
  These results form the algebraic foundation for deeper theorems like 
  Ax-Kochen-Ershov and Morley's categoricity theorem.
-/


open FirstOrder Cardinal

universe u v

open ModelTheoryBridge

variable {L : FirstOrder.Language.{u, v}}

/-! ## Section 1: Isomorphic Structures and Elementary Equivalence -/

-- !-- An L-isomorphism factors through an elementary embedding, giving elem. equivalence. -- !--

/-! ## Section 2: Complete Theories and Elementary Equivalence -/

-- !-- For each sentence φ, completeness of T gives T ⊨ φ or T ⊨ ¬φ.
--     Since both M and N are models of T, they agree on φ in both cases. -- !--

/-! ## Section 3: Complete Theory Characterization -/

-- !-- For the forward direction, T ⊨ φ implies M ⊨ φ since M is a model.
--     For the reverse, if M ⊨ φ but T ⊨ ¬φ, then M ⊨ ¬φ, contradiction. -- !--

/-! ## Section 4: Elementary Equivalence Preserves Model Relation -/

-- !-- If φ ∈ T and M ⊨ T then M ⊨ φ. Since M ≡ N, also N ⊨ φ. -- !--

/-! ## Section 5: Elementary Equivalence as an Equivalence Relation -/




/-! ## Section 6: κ-Categoricity -/


/-! ## Section 7: Categorical Theories and Elementary Equivalence -/

-- !-- If T is κ-categorical and M, N are models of size κ, then M ≅ N by categoricity,
--     so M ≡ N since isomorphism → elementary embedding → elementary equivalence. -- !--

/-! ## Section 8: Complete Theory of a Structure is Complete -/

-- !-- Th(M) is complete: satisfiable (M witnesses) and decides every sentence. -- !--

/-! ## Section 9: Completeness Characterization via Elementary Equivalence -/

-- !-- Use the hypothesis to show all models have the same complete theory as
--     the witness model M. Since Th(M) is always complete, T is complete. -- !--


open ModelTheoryBridge in
theorem solution    {T : L.Theory} (hT : T.IsComplete)
    {M : Type*} {N : Type*} [L.Structure M] [L.Structure N]
    [M ⊨ T] [N ⊨ T] [Nonempty M] [Nonempty N] :
    L.ElementarilyEquivalent M N := by
  change L.completeTheory M = L.completeTheory N
  ext φ
  simp only [Language.completeTheory, Set.mem_setOf_eq]
  obtain ⟨_, h⟩ := hT
  rcases h φ with hφ | hφ
  · exact ⟨fun _ => hφ.realize_sentence N, fun _ => hφ.realize_sentence M⟩
  · constructor
    · intro hMφ
      have := hφ.realize_sentence M
      simp [Language.Sentence.Realize, Language.Formula.realize_not] at this
      exact absurd hMφ this
    · intro hNφ
      have := hφ.realize_sentence N
      simp [Language.Sentence.Realize, Language.Formula.realize_not] at this
      exact absurd hNφ this
