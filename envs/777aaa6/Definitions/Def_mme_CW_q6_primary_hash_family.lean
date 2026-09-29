-- Prove2me | Definitions.Def_mme_CW_q6_primary_hash_family
-- name    : mme_CW_q6_primary_hash_family
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T17:54:45.358755+00:00
-- url     : https://prove2.me/theorems/af6be9d1-092b-42a2-b837-e36717628ce1
-- title:
--   Induced finite C-tensor fiber families for the coupled q=6 first hash
-- statement:
--   In the \(2N\)-th power of the coupled Coppersmith--Winograd constituent, a coarse address is a triple of grade words. The supported coordinate types are exactly \((0,0,0)\), \((1,1,1)\), \((0,1,2)\), and \((1,0,2)\). An exact \((N,L,G)\)-profile address has balanced first and second marginals \((N,N,0)\) and third marginal \((L,L,2G)\).
--
--   A primary hash family consists of \(A\) outer fibers, each containing \(H>0\) exact-profile addresses. Mode-zero and mode-one words are globally injective. All entries in one fiber share their mode-two word, while different fibers have different mode-two words. Finally, the family is induced: a supported mixed address assembled from a retained mode-zero word, a retained mode-one word, and a retained mode-two word must use the same intended first two entries and the same outer fiber.
--
--   This is the finite incidence object created by Salem--Spencer hashing and collision pruning on CW90 journal p. 271. It deliberately records the shared mode-two coordinate inside a C-tensor fiber; the \(H\) entries are not declared independent in all three tensor modes. The structure contains no tensor restriction and therefore cleanly separates finite hashing from tensor realization.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270--271: balanced X/Y words, the L/L/2G Z-profile, Salem--Spencer hashing, deletion of shared X/Y blocks, and C-tensors over <1,H,1>; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Fin
import Mathlib.Algebra.BigOperators.Fin

namespace MME

def CWQ6CoupledAddress (N : ℕ) : Type :=
  Fin 3 → Fin (2 * N) → Fin 3

def cwQ6CoupledAddressType {N : ℕ} (a : CWQ6CoupledAddress N)
    (j : Fin (2 * N)) : Fin 3 → Fin 3 :=
  fun i => a i j

def CWQ6CoupledCoordinatewiseSupported {N : ℕ}
    (a : CWQ6CoupledAddress N) : Prop :=
  ∀ j : Fin (2 * N),
    (a 0 j = 0 ∧ a 1 j = 0 ∧ a 2 j = 0) ∨
    (a 0 j = 1 ∧ a 1 j = 1 ∧ a 2 j = 1) ∨
    (a 0 j = 0 ∧ a 1 j = 1 ∧ a 2 j = 2) ∨
    (a 0 j = 1 ∧ a 1 j = 0 ∧ a 2 j = 2)

def cwQ6CoupledMarginalMultiplicity
    (N L G : ℕ) (i r : Fin 3) : ℕ :=
  if i = 0 then
    if r = 0 then N else if r = 1 then N else 0
  else if i = 1 then
    if r = 0 then N else if r = 1 then N else 0
  else
    if r = 0 then L else if r = 1 then L else 2 * G

def CWQ6ExactCoupledAddress (N L G : ℕ) : Type :=
  {a : CWQ6CoupledAddress N //
    CWQ6CoupledCoordinatewiseSupported a ∧
    ∀ i r : Fin 3,
      (Finset.univ.filter (fun j : Fin (2 * N) => a i j = r)).card =
        cwQ6CoupledMarginalMultiplicity N L G i r}

def cwQ6CoupledMixedAddress {N : ℕ}
    (x y z : CWQ6CoupledAddress N) : CWQ6CoupledAddress N
  | ⟨0, _⟩ => x 0
  | ⟨1, _⟩ => y 1
  | ⟨2, _⟩ => z 2
  | ⟨_ + 3, h⟩ => absurd h (by omega)

structure CWQ6PrimaryHashFamily (N L G A H : ℕ) where
  hHpos : 0 < H
  entry : Fin A × Fin H → CWQ6ExactCoupledAddress N L G
  xInjective : Function.Injective (fun p => (entry p).1 0)
  yInjective : Function.Injective (fun p => (entry p).1 1)
  zSameFiber : ∀ (a : Fin A) (h k : Fin H),
    (entry (a, h)).1 2 = (entry (a, k)).1 2
  zSeparatesFibers : ∀ (a b : Fin A) (h k : Fin H),
    (entry (a, h)).1 2 = (entry (b, k)).1 2 → a = b
  induced : ∀ p q r : Fin A × Fin H,
    CWQ6CoupledCoordinatewiseSupported
      (cwQ6CoupledMixedAddress (entry p).1 (entry q).1 (entry r).1) →
    p = q ∧ p.1 = r.1

end MME


