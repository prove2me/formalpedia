-- Prove2me | Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumChannel_part_4
-- name    : CRCD_Quantum_QuantumMechanics_QuantumChannel_part_4
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T23:51:09.070988+00:00
-- url     : https://prove2.me/theorems/874a11be-f3a7-4e86-b4d1-c764ffc2eb21
-- title:
--   Finite-dimensional equivalence of complete positivity, Choi positivity, and dilations
-- statement:
--   Let $H_1,H_2$ be finite-dimensional complex Hilbert spaces, let $b=(b_i)_{i\in\iota}$ be any complex-linear basis of $H_1$ indexed by a finite type, and let $\Phi:\mathcal L(H_1)\to\mathcal L(H_2)$ be a complex-linear superoperator. Using the preceding Choi, Kraus and partial-trace constructions, this part completes the finite-dimensional Choi characterization:
--   $$
--   \Phi\text{ is completely positive}\quad\Longleftrightarrow\quad C_b(\Phi)\ge0.
--   $$
--   No orthonormality of $b$, trace-preservation condition on $\Phi$, or nonzero-dimension hypothesis on the spaces is added. The part proves that complete positivity yields a finite Kraus representation, including one with exactly $\operatorname{rank}C_b(\Phi)$ terms, and yields a finite-dimensional Stinespring representation. A rank-sized Kraus representation yields a Stinespring representation whose environment has dimension exactly $\operatorname{rank}C_b(\Phi)$. Conversely, any Stinespring representation $\Phi(X)=\mathrm{Tr}_{\mathrm{right}}(WXW^*)$ implies complete positivity. Together with the implications already supplied by predecessor parts, these facts make the Choi, Kraus and Stinespring descriptions interchangeable while retaining the explicit rank bounds.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumMechanics/QuantumChannel.lean#L2351-L2490

import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumChannel_part_3
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumState

/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/








-- These typeclasses are kept on several declarations as part of a stable API
-- (e.g. matching downstream signatures), even when the type does not literally
-- mention them; silence the Mathlib hygiene linters for the whole file.
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace QuantumChannel

open QuantumState
open TensorProduct

universe u v w

section Definition

-- The set of linear maps


section ContinuousLinearMapsAreCStarAlgebras





















end ContinuousLinearMapsAreCStarAlgebras


-- The structure of quantum channels


variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

-- def: Partial trace (1.121) https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
-- Tr₂(X) for X ∈ L(ℋ₁⊗ℋ₂)







-- It may be neccesary to add some lemmas to use l_tensor_equiv effectively















-- def: vec(A) (1.127) https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
-- vec[|u⟩⟨v|] := |u⟩⊗|v⟩ : (ℋ₁ →L[ℂ] ℋ₂) → ℋ₂⊗ℋ₁






-- (1.131) (1.132) https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
-- Lemma 5.12 http://www.ueltschi.org/AZschool/notes/EricCarlen.pdf
-- For any qudit ℋ, any A,B ∈ L(ℋ), and any K ∈ L(ℋ),
-- ⟨ vec[K] ∣ (A ⊗ B) vec[K] ⟩ = Tr[K† A K B.transpose]






















-- def: Choi operator (2.64) https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- J(Φ) := (Φ⊗id)(vec[I(ℋ₂⊗ℋ₁)] vec[I(ℋ₂⊗ℋ₁)]†) for Φ ∈ T(ℋ₁,ℋ₂)

-- (1.57) in https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf












end Definition

section RepresentationsOfChannels

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]

-- Proposition 2.17 https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudit ℋ, and any P ∈ Pos(ℋ),
-- the map Φ(α):=αP ∈ T(ℂ,ℋ) is a completely positive ContinuourLinearMap.

-- Proposition 2.18 and its remark https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudits ℋ₁, ℋ₂, and any Φ ∈ T(ℋ₁,ℋ₂),
-- if Φ is a completely positive ContinuourLinearMap,
-- the adjoint map of Φ is a completely positive ContinuourLinearMap.

-- Corollary 2.19 https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudit ℋ, Tr ∈ T(ℋ,ℂ) is a completely positive ContinuourLinearMap.

-- Proposition 2.20 https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudits ℋ₁, ℋ₂, and any Φ ∈ T(ℋ₁,ℋ₂),
-- J(Φ)=∑_{a∈Σ} vec(Aₐ) vec(Bₐ)†
-- if and only if
-- for ℋ₃=ℂ^Σ, A,B∈(ℋ₁→L[ℂ]ℋ₂⊗ℋ₃) defined as
-- A=∑_{a∈Σ}Aₐ⊗eₐ,
-- B=∑_{a∈Σ}Aₐ⊗eₐ,
-- it holds for all X∈L(X) that
-- Φ(X)=Tr₃[Aₐ X Bₐ†]

-- Theorem 2.22 https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudits ℋ₁, ℋ₂, and any Φ ∈ T(ℋ₁,ℋ₂), the following statements are equivalent:
-- 1: Φ is a completely positive ContinuosLinearMap;
-- 2: J(Φ) ∈ Pos(ℋ₂⊗ℋ₁);
-- 3: ∃qudit ℋ₃, ∃A∈(ℋ₁→L[ℂ]ℋ₂⊗ℋ₃), Φ(X)=Tr₃[A X A†]





variable {ι : Type*} [DecidableEq ι] [Fintype ι]



























































































































































































































































-- (1) → (2)


-- (3) → (5)


















-- (4) → (6)


-- (5) → (7)
theorem rank_kraus_to_rank_stinespring
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasRankKraus b Φ → HasRankStinespring b Φ := by
  rintro ⟨κ, hκ, hκ', hcard, hΦ⟩
  letI : DecidableEq κ := hκ
  letI : Fintype κ := hκ'
  refine ⟨EuclideanSpace ℂ κ, inferInstance, ?_, ?_⟩
  · rw [finrank_kraus_environment]
    exact hcard
  · exact fixed_kraus_to_stinespring (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) Φ hΦ















-- (6) → (1)
theorem stinespring_to_cp
    (Φ : T ℋ₁ ℋ₂) :
    HasStinespring Φ → IsCompletelyPositive Φ := by
  rintro ⟨ℋ₃, inst, hΦ⟩
  letI : Qudit ℋ₃ := inst
  exact (isCompletelyPositive_iff_cstarMatrix_nonneg Φ).mpr
    (stinespring_cstarMatrix_nonneg Φ hΦ)



theorem cp_to_choi
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ → ChoiPositive b Φ :=
  tensor_to_choi b Φ ∘
    cp_to_tensor Φ

theorem cp_to_rank_kraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ → HasRankKraus b Φ :=
  choi_to_rank_kraus b Φ ∘
    cp_to_choi b Φ

theorem cp_to_kraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ → HasKraus Φ :=
  rankKraus_to_kraus b Φ ∘
    cp_to_rank_kraus b Φ

theorem cp_to_stinespring
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ → HasStinespring Φ :=
  kraus_to_stinespring Φ ∘
    cp_to_kraus b Φ



theorem choi_to_cp
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    ChoiPositive b Φ → IsCompletelyPositive Φ :=
  stinespring_to_cp Φ ∘
    rankStinespring_to_stinespring b Φ ∘
    rank_kraus_to_rank_stinespring b Φ ∘
    choi_to_rank_kraus b Φ









theorem cp_iff_choi
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis κ ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ ↔ ChoiPositive b Φ := by
  exact ⟨cp_to_choi b Φ, choi_to_cp b Φ⟩
end RepresentationsOfChannels
end QuantumChannel


