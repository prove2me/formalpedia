-- Prove2me | Definitions.Def_Shamir1979_Model
-- name    : Shamir1979_Model
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-29T07:49:39.672009+00:00
-- url     : https://prove2.me/theorems/4fc960aa-08f2-4c14-84b4-91e6b13907d7
-- title:
--   Shamir’s finite-field sharing experiment and observation probabilities
-- statement:
--   This bundle defines a concrete finite experiment for Shamir's polynomial threshold construction. For a prime p and threshold k, randomness is a vector of k-1 elements of ZMod p; the sharing polynomial has the secret as constant coefficient. Participants use the public identifiers 1 through n. A coalition observes the function assigning its members their polynomial evaluations. Reconstruction is an explicit Lagrange sum evaluated at zero, with a product omitting the location being reconstructed. Event probabilities are exact rational counts over the entire finite coefficient-vector sample space. Auxiliary interfaces describe unions of polynomial locations held by a coalition and finite collections of independently sampled sharing editions. The epoch sample space is the full product of coefficient-vector spaces, which makes the independence convention explicit. No reconstruction, privacy, or interpolation theorem is assumed in these definitions. The functions are total; the proposed correctness and privacy targets impose 1 ≤ k ≤ n < p.
-- source:
--   Adi Shamir, How to Share a Secret, Communications of the ACM 22(11), 612–613 (1979), https://doi.org/10.1145/359168.359176, §2, p. 613: polynomial construction, interpolation, uniform sampling, and properties (2)–(4)

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Defs

/-!
# Finite experiments for Shamir's threshold scheme

Adi Shamir, “How to Share a Secret,” Communications of the ACM 22(11),
612–613 (1979), §2. DOI: https://doi.org/10.1145/359168.359176.
The k-1 coefficients are independently uniform, including zero; polynomial
bounds are therefore degree < k. Participants use the public identifiers 1,...,n.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace Shamir1979
universe u

abbrev Coins (p k : Nat) := Fin (k-1) → ZMod p

abbrev Observation (p : Nat) {n : Nat} (Γ : Finset (Fin n)) :=
  {i : Fin n // i ∈ Γ} → ZMod p

def sharingPolynomial {p k : Nat} (secret : ZMod p) (coins : Coins p k) :
    Polynomial (ZMod p) :=
  Polynomial.C secret + ∑ j : Fin (k-1), Polynomial.monomial (j.val+1) (coins j)

def point {p n : Nat} (i : Fin n) : ZMod p := ((i.val+1 : Nat) : ZMod p)

def share {p n k : Nat} (secret : ZMod p) (coins : Coins p k) (i : Fin n) : ZMod p :=
  (sharingPolynomial secret coins).eval (point i)

def observe {p n k : Nat} (Γ : Finset (Fin n)) (secret : ZMod p)
    (coins : Coins p k) : Observation p Γ := fun i => share secret coins i.val

def recover {p n : Nat} [Fact (Nat.Prime p)] (Γ : Finset (Fin n))
    (values : Observation p Γ) : ZMod p := by
  classical
  exact ∑ i : {i : Fin n // i ∈ Γ}, values i *
    ∏ j : {j : Fin n // j ∈ Γ},
      if j=i then 1 else (-point (p := p) j.val) / (point (p := p) i.val - point (p := p) j.val)

def fiberCount {p n k : Nat} [Fact (Nat.Prime p)] (Γ : Finset (Fin n))
    (secret : ZMod p) (values : Observation p Γ) : Nat := by
  classical
  exact (Finset.univ.filter fun coins : Coins p k => observe Γ secret coins = values).card

def observationProbability {p n k : Nat} [Fact (Nat.Prime p)] (Γ : Finset (Fin n))
    (secret : ZMod p) (values : Observation p Γ) : Rat :=
  (fiberCount (k := k) Γ secret values : Rat) / (Fintype.card (Coins p k) : Rat)

def heldLocations {A : Type u} {n : Nat} (holdings : A → Finset (Fin n))
    (coalition : Finset A) : Finset (Fin n) := by
  classical
  exact coalition.biUnion holdings

def epochObservation {p n k : Nat} {E : Type u} (groups : E → Finset (Fin n))
    (secret : ZMod p) (coins : E → Coins p k) : (e : E) → Observation p (groups e) :=
  fun e => observe (groups e) secret (coins e)

def epochProbability {p n k : Nat} [Fact (Nat.Prime p)] {E : Type u} [Fintype E]
    (groups : E → Finset (Fin n)) (secret : ZMod p)
    (values : (e : E) → Observation p (groups e)) : Rat := by
  classical
  exact ((Finset.univ.filter fun coins : E → Coins p k =>
    epochObservation groups secret coins = values).card : Rat) /
      (Fintype.card (E → Coins p k) : Rat)

end Shamir1979


