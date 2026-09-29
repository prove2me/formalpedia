-- Prove2me | Definitions.Def_mme_stothers_general_affine_hash
-- name    : mme_stothers_general_affine_hash
-- status  : Definition
-- author  : @allychan327
-- created : 2026-09-08T17:01:06.858686+00:00
-- url     : https://prove2.me/theorems/3e721c16-05ad-4de0-ac41-c6d56f18ae58
-- title:
--   Affine-hash data for a general outer profile
-- statement:
--   **Affine-hash data for a general integral outer profile.**
--
--   The $d=8$ versions of the three hashes in the proof of Davie--Stothers Lemma 3.3, stated over an
--   arbitrary integral ten-class profile $\beta$ rather than the published fixed witness. For an odd
--   prime modulus $p$, a weight vector $w$ on the $N = 3Dm$ positions and an affine offset $b_0$, the
--   three mode words of an address are hashed by
--
--   $$X(x) = \tfrac12\sum_k 2x_k w_k,\qquad Y(y) = \tfrac12\Bigl(2b_0 + \sum_k 2y_k w_k\Bigr),\qquad
--   Z(z) = \tfrac12\Bigl(b_0 + \sum_k (8 - z_k)w_k\Bigr),$$
--
--   all in $\mathbb Z/p$. The doubled presentations are recorded separately so that division by two is
--   deferred until the modulus is known to be odd.
--
--   On top of these the file records, all parameterized by $\beta$: the family of marginal-supported
--   addresses retained at one hash state (those whose three hashes agree on a common value in a
--   prescribed residue set $S$), the set of states retaining a given address, the ambient universe of
--   marginal-supported addresses, the universe of hash states, the retained family as a function of the
--   state, and the exact-profile target edges and target--ambient collisions of the full ambient
--   universe.
--
--   There are no counting or extraction claims here; this is interface data only. Names are prefixed
--   `gen` so that nothing collides with the published fixed-witness affine-hash data, which is recovered
--   by taking $\beta$ to be the stationary witness.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, proof of Lemma 3.3; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Prod
import Definitions.Def_mme_stothers_general_outer_profile

open MME BigOperators

namespace MME.StothersFourth

set_option autoImplicit false

/-!
# Affine-hash data for a general integral outer profile

These are the `d = 8` versions of the three hashes in the proof of
Davie--Stothers Lemma 3.3.  The doubled presentation avoids division by two
until the modulus is known to be odd.
-/

def genHashDoubledX
    {R : Type} [CommSemiring R] {N : ℕ}
    (w : Fin N → R) (x : Fin N → Fin 9) : R :=
  ∑ k, ((2 * (x k).val : ℕ) : R) * w k

def genHashDoubledY
    {R : Type} [CommSemiring R] {N : ℕ}
    (b0 : R) (w : Fin N → R) (y : Fin N → Fin 9) : R :=
  2 * b0 + ∑ k, ((2 * (y k).val : ℕ) : R) * w k

def genHashDoubledZ
    {R : Type} [CommSemiring R] {N : ℕ}
    (b0 : R) (w : Fin N → R) (z : Fin N → Fin 9) : R :=
  b0 + ∑ k, ((8 - (z k).val : ℕ) : R) * w k

def genHashXMod {M N : ℕ}
    (w : Fin N → ZMod M) (x : Fin N → Fin 9) : ZMod M :=
  (2 : ZMod M)⁻¹ * genHashDoubledX w x

def genHashYMod {M N : ℕ}
    (b0 : ZMod M) (w : Fin N → ZMod M)
    (y : Fin N → Fin 9) : ZMod M :=
  (2 : ZMod M)⁻¹ * genHashDoubledY b0 w y

def genHashZMod {M N : ℕ}
    (b0 : ZMod M) (w : Fin N → ZMod M)
    (z : Fin N → Fin 9) : ZMod M :=
  (2 : ZMod M)⁻¹ * genHashDoubledZ b0 w z

/-- The full marginal-supported edge set retained at one affine hash state. -/
noncomputable def genHashRetainedEdges
    (base : Fin 10 → ℕ) (m p : ℕ) (S : Finset ℕ) (b0 : ZMod p)
    (w : Fin (genOuterLength base m) → ZMod p) :
    Finset (GenMarginalSupportedAddress base m) := by
  classical
  letI : Fintype (GenOuterAddress base m) :=
    inferInstanceAs (Fintype
      (Fin 3 → Fin (genOuterLength base m) → Fin 9))
  letI : Fintype (GenMarginalSupportedAddress base m) :=
    inferInstanceAs (Fintype
      {a : GenOuterAddress base m //
        GenCoordinatewiseSupported a ∧ GenMarginallyRegular a})
  exact Finset.univ.filter (fun a ↦
    ∃ s ∈ S,
      genHashXMod w (a.1 0) = (s : ZMod p) ∧
      genHashYMod b0 w (a.1 1) = (s : ZMod p) ∧
      genHashZMod b0 w (a.1 2) = (s : ZMod p))

/-- An extra unused weight coordinate makes the affine-state fiber size a
clean power `p^N`; the separate `ZMod p` coordinate is the affine offset. -/
noncomputable def genHashStatesRetainingAddress
    (base : Fin 10 → ℕ) (m p : ℕ) [NeZero p] (S : Finset ℕ)
    (a : GenMarginalSupportedAddress base m) :
    Finset ((Fin (genOuterLength base m + 1) → ZMod p) × ZMod p) := by
  classical
  exact Finset.univ.filter (fun q ↦
    a ∈ genHashRetainedEdges base m p S q.2
      (fun k ↦ q.1 k.castSucc))

noncomputable def genHashMarginalUniverse (base : Fin 10 → ℕ) (m : ℕ) :
    Finset (GenMarginalSupportedAddress base m) := by
  classical
  letI : Fintype (GenOuterAddress base m) :=
    inferInstanceAs (Fintype
      (Fin 3 → Fin (genOuterLength base m) → Fin 9))
  letI : Fintype (GenMarginalSupportedAddress base m) :=
    inferInstanceAs (Fintype
      {a : GenOuterAddress base m //
        GenCoordinatewiseSupported a ∧ GenMarginallyRegular a})
  exact Finset.univ

noncomputable def genHashStateUniverse
    (base : Fin 10 → ℕ) (m p : ℕ) [NeZero p] :
    Finset ((Fin (genOuterLength base m + 1) → ZMod p) × ZMod p) := by
  classical
  exact Finset.univ

noncomputable def genHashEdgesAtState
    (base : Fin 10 → ℕ) (m p : ℕ) [NeZero p] (S : Finset ℕ)
    (q : (Fin (genOuterLength base m + 1) → ZMod p) × ZMod p) :
    Finset (GenMarginalSupportedAddress base m) :=
  genHashRetainedEdges base m p S q.2 (fun k ↦ q.1 k.castSucc)

noncomputable def genHashAllTargetEdges (base : Fin 10 → ℕ) (m : ℕ) :
    Finset (GenMarginalSupportedAddress base m) :=
  genExactTargetEdges (genHashMarginalUniverse base m)

noncomputable def genHashAllTargetAmbientCollisions (base : Fin 10 → ℕ) (m : ℕ) :
    Finset (GenMarginalSupportedAddress base m ×
      GenMarginalSupportedAddress base m) :=
  genTargetAmbientCollisions (genHashMarginalUniverse base m)

end MME.StothersFourth


