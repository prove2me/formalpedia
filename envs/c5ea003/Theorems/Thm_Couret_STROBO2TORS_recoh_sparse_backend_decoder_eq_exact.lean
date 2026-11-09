-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_sparse_backend_decoder_eq_exact
-- name    : Couret.STROBO2TORS.recoh_sparse_backend_decoder_eq_exact
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:57:17.460192+00:00
-- url     : https://prove2.me/theorems/7b2b9f56-029f-4616-910d-eda014d16c68
-- title:
--   The sparse backend equals exact decoding
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $P_\chi(S)=\sum_{x\in S}\chi(x)$, and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$, where $Q_S$ counts ordered sums and $B$ is a bank of complex additive characters. Assume $G$ finite. Supply a finite $U\subseteq G$, square data $R:G\to\mathbb N$ supported in $U$, a sound and complete partial half solver $h$, a bank $B=(\chi_i)_{i<m}$ and observations $o_i$. Supply selected indices $j:a<r\mapsto j(a)<m$ and $e:H\simeq\mathbb F_2^r$ with $\chi_{j(a)}(u)=(-1)^{e(u)_a}$, and assume all selected probes are nonzero on every triple. For selected coordinates supply depths $k_a^{(2)}$, roots primitive of order $2^{k_a^{(2)}+1}$, support exponent encodings evaluating to the selected probes for every support, and observed exponent lists evaluating to $o_{j(a)}$. For every bank index supply a prime $p_i$, depth $k_i$, primitive root of order $p_i^{k_i+1}$, and support/observed exponent encodings evaluating respectively to every support probe and $o_i$. Then $$D_{\mathrm{sparse}}(U,R,h,e,\mathrm{selected\ encodings},\mathrm{full\ encodings})=D_B(R,o).$$
--
--   This theorem retains all encoding, primitive-root, and nonvanishing assumptions explicitly.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohExactSignBackend.lean, lines 203–241; source file SHA-256 f99e3408f62032866dd7332e37aea90148e1e51601887993b2026a97b35d79dd; theorem Couret.STROBO2TORS.recoh_sparse_backend_decoder_eq_exact

import Aesop
import Definitions.Def_Couret_RecohExactSignBackend_8d2941f5c2c9
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_checked_fast_decoder_eq_exact
import Theorems.Thm_Couret_STROBO2TORS_recoh_normalized_sparse_equal_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_recover_translation_coordinate
import Theorems.Thm_Couret_STROBO2TORS_recoh_sign_bit_from_bool_eq
import Theorems.Thm_Couret_STROBO2TORS_recoh_sign_recovery_spec
import Theorems.Thm_Couret_STROBO2TORS_recoh_sparse_observation_check_iff
import Definitions.Def_Couret_RecohFastDecoder_5bb89f11acce
import Definitions.Def_Couret_RecohCyclotomicNormalization_6797485e207c
import Definitions.Def_Couret_RecohSparseObservation_6dd9be0e8eb2

set_option autoImplicit false

/-!
Computable comparison bits and their refinement of complex sign recovery.

The comparison booleans are supplied by an exact arithmetic backend.  Only
their correctness proposition mentions complex numbers.  The recovered
coordinate vector and transport through a supplied coordinate equivalence
are ordinary Lean definitions, with no complex equality decision at runtime.
-/

namespace Couret.STROBO2TORS





variable {G : Type*} [AddCommGroup G] {r : ℕ}

local notation "H₂" => recohTorsionSubgroup (G := G) 2







variable [DecidableEq G]

theorem recoh_sparse_backend_decoder_eq_exact [Fintype G] {m : ℕ}
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (bank : Fin m → AddChar G ℂ) (obs : Fin m → ℂ)
    (index : Fin r → Fin m) (e : H₂ ≃+ (Fin r → ZMod 2))
    (k2 : Fin r → ℕ) (enc2 : Fin r → Finset G → List ℕ)
    (obs2 : Fin r → List ℕ) (ζ2 : Fin r → ℂ)
    (p k : Fin m → ℕ) (enc : Fin m → Finset G → List ℕ)
    (obsExp : Fin m → List ℕ) (ζ : Fin m → ℂ)
    (hhalf : RecohHalfSolverSpec half)
    (hR : ∀ z, R z ≠ 0 → z ∈ U)
    (hζ2 : ∀ i, IsPrimitiveRoot (ζ2 i) (2 ^ (k2 i + 1)))
    (henc2 : ∀ i B, ((enc2 i B).map ((ζ2 i) ^ ·)).sum =
      recohSupportProbe (bank (index i)) B)
    (hobs2 : ∀ i, ((obs2 i).map ((ζ2 i) ^ ·)).sum = obs (index i))
    (hcoord : ∀ (u : H₂) (i : Fin r),
      bank (index i) (u : G) = if e u i = 0 then 1 else -1)
    (hnonzero : ∀ i (B : Finset G), B.card = 3 →
      recohSupportProbe (bank (index i)) B ≠ 0)
    (hp : ∀ i, (p i).Prime)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) ((p i) ^ (k i + 1)))
    (henc : ∀ i B, ((enc i B).map ((ζ i) ^ ·)).sum = recohSupportProbe (bank i) B)
    (hobs : ∀ i, ((obsExp i).map ((ζ i) ^ ·)).sum = obs i) :
    recohSparseBackendDecoder U R half e k2 enc2 obs2 p k enc obsExp =
      recohExactDecoder bank (R, obs) := by sorry




end Couret.STROBO2TORS
