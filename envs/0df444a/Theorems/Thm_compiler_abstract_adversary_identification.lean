-- Prove2me | Theorems.Thm_compiler_abstract_adversary_identification
-- name    : compiler_abstract_adversary_identification
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-23T21:56:04.826802+00:00
-- url     : https://prove2.me/theorems/f4aa1d67-ccc1-43d1-9dcf-9582f05b32a2
-- title:
--   General-adversary identification algorithm with an explicit linear query budget
-- statement:
--   Let a finite family of Boolean oracles be indexed by hidden labels. Suppose positive semidefinite matrices satisfy the dual adversary distinguishing constraints and have diagonal objective at most T. Then a fixed sequence of input-independent complex unitaries, alternating with the controlled phase oracle, identifies every hidden label with probability at least 2/3 using at most 73(T+1) oracle slots.
--
--   The workspace is an explicit direct sum of a public clock-and-output register and a private query register. The initial public state is independent of the hidden label. This establishes the state-conversion part of the Section 4 adversary compiler in the unrestricted finite-dimensional query model; realization as a gates12 OracleCircuit is a separate theorem.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331v3, Section 4.5.1, equations (129)–(134), pp. 50–52. Explicit constant obtained by choosing N=ceil(72(T+1)) in the catalyst clock construction.

import Definitions.Def_QuantumLTF_Majority_CompilerModel

theorem compiler_abstract_adversary_identification {ι σ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype σ]
    (f : ι → σ → Bool) (X : σ → Matrix ι ι ℝ)
    (hPSD : ∀ s, (X s).PosSemidef)
    (hdual : ∀ a b, a ≠ b → (∑ s, if f a s ≠ f b s then X s a b else 0) = 1)
    (T : ℝ) (hT : 0 ≤ T) (hcost : ∀ a, ∑ s, X s a a ≤ T) :
    ∃ (ω : Type) (_ : Fintype ω) (N : ℕ), 0 < N ∧ (N : ℝ) ≤ 73 * (T+1) ∧
      let E := EuclideanSpace ℂ ((Fin N × Option ι) ⊕ (σ × ω))
      let O : ι → E ≃ₗᵢ[ℂ] E := fun a => compiler_sign_oracle
        (Sum.elim (fun _ => false) (fun j : σ × ω => f a j.1))
      let start : E := (((Real.sqrt N)⁻¹ : ℝ) : ℂ) • compiler_left (compiler_clock_start N)
      ∃ U : ℕ → E ≃ₗᵢ[ℂ] E, ∀ a,
        (∑ j, if compiler_success_event a j then
          ‖compiler_clock_run U (O a) N start j‖ ^ 2 else 0) ≥ (2/3 : ℝ) := by sorry
