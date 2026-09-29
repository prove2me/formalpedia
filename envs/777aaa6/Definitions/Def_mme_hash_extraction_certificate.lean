-- Prove2me | Definitions.Def_mme_hash_extraction_certificate
-- name    : mme_hash_extraction_certificate
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-12T08:55:07.92176+00:00
-- url     : https://prove2.me/theorems/f536e5d2-cb45-495b-90b4-3336c0de2b8c
-- title:
--   Finite hash bundles and actual CW extraction certificates
-- statement:
--   A finite hash bundle records finitely many physical recursive affine-hash problems, each with its own parameters and state-dependent usable family. Its budget asks for the ambient X-degree inequality and a total usable-incidence fraction of at least $7/8$.
--
--   For a hash factor $j$, set $L_j=|T_j||S_j|/(2p_j^2)$. A bundle also records a positive grouping cost $H$, matrix dimensions $a,b,c$, and a source power $s$. Its algebraic realization predicate over a field $K$ requires every tuple of usable X-isolated families $I_j$, with $|I_j|\ge L_j$, to give the actual restriction
--
--   $$\bigoplus_{\lfloor\prod_j|I_j|/H\rfloor}\langle a,b,c\rangle\;\preceq\;\operatorname{sym}_6(CW_5^{\otimes4})^{\otimes s}.$$
--
--   The conservative scalar rate is
--
--   $$R_\tau=\left(\frac{\prod_jL_j}{H}-1\right)(abc)^\tau.$$
--
--   The realization predicate is an explicit unproved algebraic obligation, including ownership, recursive construction and repair. Defining it does not establish a restriction or certify any numerical witness. These interfaces support a finite assembly theorem and a connected reduction of the live surplus goal.
-- source:
--   Auxiliary integration interface designed from arXiv:2404.16349v2, Sections 5--6 (regional hashing, interface recursion and hole repair) and Section 7. https://arxiv.org/html/2404.16349v2. The bundle and conservative floor-adjusted rate are formalization interfaces, not named definitions in the paper.

import Definitions.Def_mme_recursive_x_hash_families
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_six_symmetrized_tau_value

open BigOperators MME.RecursiveThinSplit MME.RecursiveXHash
set_option autoImplicit false
universe u

namespace MME.HashExtraction

/-- One physical affine hash, with a specified family of usable retained copies.
Usability can encode the simultaneous Y/Z hole bounds needed for later repair. -/
structure HashData where
  half : ℕ
  R : ℕ
  parent : Fin R → Fin 3 → ℕ
  n : Fin R → ℕ
  m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ
  N : ℕ
  p : ℕ
  prime : p.Prime
  odd : Odd p
  grade_lt : half < p
  positions : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)
  labels : Finset ℕ
  labels_range : labels ⊆ Finset.range (p / 2)
  labels_free : ThreeAPFree (labels : Set ℕ)
  good : ((Fin (N + 2) → ZMod p) × ZMod p) → Finset (Address half R parent n)

instance HashData.modulus_neZero (d : HashData) : NeZero d.p := ⟨d.prime.ne_zero⟩

abbrev HashData.State (d : HashData) := (Fin (d.N + 2) → ZMod d.p) × ZMod d.p
abbrev HashData.Edge (d : HashData) := Address d.half d.R d.parent d.n

noncomputable def HashData.retained (d : HashData) (q : d.State) : Finset d.Edge :=
  bucketed d.m d.positions (d.labels.image (fun a : ℕ ↦ (a : ZMod d.p))) q

/-- The degree bound and the total usable-incidence estimate are separate,
explicit finite obligations. All losses are measured before choosing the state. -/
noncomputable def HashData.Budget (d : HashData) : Prop :=
  8 * (ambient (n := d.n) d.m).card ≤
    d.p * ((ambient (n := d.n) d.m).image (block 0)).card ∧
  (7 / 8 : ℝ) * ((target (n := d.n) d.m).card * d.labels.card * (d.p : ℝ) ^ (d.N + 1)) ≤
    ∑ q, ((((target d.m).filter (fun a ↦ a ∈ d.retained q)) ∩ d.good q).card : ℝ)

noncomputable def HashData.Selection (d : HashData) (q : d.State) (I : Finset d.Edge) : Prop :=
  I ⊆ target d.m ∧ I ⊆ d.retained q ∧ I ⊆ d.good q ∧
  ∀ a ∈ I, ∀ b ∈ d.retained q, block 0 a = block 0 b → a = b

noncomputable def HashData.lower (d : HashData) : ℝ :=
  ((target (n := d.n) d.m).card : ℝ) * d.labels.card / (2 * (d.p : ℝ) ^ 2)

/-- A finite bundle permits separate hashes in distinct regions or recursive
factors. The source theorem must realize their simultaneous selected product. -/
structure Data where
  factors : ℕ
  hash : Fin factors → HashData
  repairCopies : ℕ
  repair_pos : 0 < repairCopies
  a : ℕ
  b : ℕ
  c : ℕ
  power : ℕ

/-- Exact algebraic obligation, including ownership, recursion and hole repair.
Every tuple of sufficiently large usable isolated families must yield the displayed direct sum
from the literal six-symmetrized fourth CW tensor over the chosen field. -/
noncomputable def Data.Realizes (d : Data) (K : Type u) [Field K] : Prop :=
  ∀ (q : ∀ j, (d.hash j).State) (I : ∀ j, Finset (d.hash j).Edge),
    (∀ j, (d.hash j).Selection (q j) (I j)) →
    (∀ j, (d.hash j).lower ≤ ((I j).card : ℝ)) →
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin ((∏ j, (I j).card) / d.repairCopies) ↦
        MMObj K d.a d.b d.c))
      ((sixSymmetrization (MME.StothersFourth.cwFourthObj K 5)).kronPow d.power)

/-- A conservative lower bound after grouping copies for repair; the subtraction
of one accounts for the integer floor. Its sign is unrestricted. -/
noncomputable def Data.rate (d : Data) (tau : ℝ) : ℝ :=
  ((∏ j, (d.hash j).lower) / d.repairCopies - 1) *
    (((d.a * d.b * d.c : ℕ) : ℝ) ^ tau)

end MME.HashExtraction


