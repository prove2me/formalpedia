-- Prove2me | Definitions.Def_mme_schonhage_pan_certificate
-- name    : mme_schonhage_pan_certificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T03:51:34.951252+00:00
-- url     : https://prove2.me/theorems/1f747276-ec2e-4a5d-bc15-b9116fbc780d
-- title:
--   Explicit characteristic-free Schönhage–Pan 156-slot certificate
-- statement:
--   This module defines the explicit polynomial family underlying the order-12 Schönhage–Pan degeneration for the direct sum $\langle1,5,22\rangle \oplus \langle11,2,5\rangle \oplus \langle10,11,1\rangle$. It introduces the three coordinate alphabets, Pan's six rank-one slot families and their signed companion, a 156-slot indexing equivalence, bases for the three target mode spaces, and the finitely supported mode maps forming the polynomial family $\Phi$. The coefficient identities are deliberately left to separate theorem nodes.
-- source:
--   Victor Y. Pan, New combinations of methods for the acceleration of matrix multiplications, Computers & Mathematics with Applications 7 (1981), 73–125, Appendix p. 125 (PDF p. 53), Tables 19.3''–19.8'' and Table 19.9; Pan attributes the arbitrary-field mapping (A2) to Schönhage.

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Definitions.Def_mme_degeneration
import Definitions.Def_mme_tensor_rank

universe u

open BigOperators Finset Polynomial


namespace PanLeanBridge

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

variable {K : Type u} [Field K]

noncomputable section

inductive Var0 where
  | a : Fin 5 → Var0
  | u : Fin 2 → Fin 11 → Var0
  | x : Fin 2 → Fin 11 → Fin 5 → Var0
  deriving DecidableEq

inductive Var1 where
  | c : Fin 2 → Fin 11 → Fin 5 → Var1
  | w : Fin 2 → Fin 5 → Var1
  | z : Fin 11 → Var1
  deriving DecidableEq

inductive Var2 where
  | b : Fin 2 → Fin 11 → Var2
  | v : Fin 11 → Fin 5 → Var2
  | y : Fin 2 → Fin 5 → Var2
  deriving DecidableEq

def delta {A : Type*} [DecidableEq A] (x y : A) : K := if x = y then 1 else 0
def sideSign (s : Fin 2) : K := if s = 0 then 1 else -1
def mon (d : ℕ) (c : K) : K[X] := Polynomial.monomial d c

def ac (q : Var0) (s : Fin 2) (i : Fin 5) : K := sideSign s * delta q (.a i)
def uc (q : Var0) (s : Fin 2) (k : Fin 11) : K := delta q (.u s k)
def xc (q : Var0) (s : Fin 2) (k : Fin 11) (i : Fin 5) : K :=
  delta q (.x s k i)
def bc (q : Var2) (s : Fin 2) (k : Fin 11) : K := delta q (.b s k)
def vc (q : Var2) (k : Fin 11) (i : Fin 5) : K := delta q (.v k i)
def yc (q : Var2) (s : Fin 2) (i : Fin 5) : K := delta q (.y s i)
def cc (q : Var1) (s : Fin 2) (k : Fin 11) (i : Fin 5) : K :=
  sideSign s * delta q (.c s k i)
def wc (q : Var1) (s : Fin 2) (i : Fin 5) : K := delta q (.w s i)
def zc (q : Var1) (k : Fin 11) : K := delta q (.z k)

def p3 (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (i : Fin 5) (k : Fin 11) : K[X] :=
  (mon 4 (ac q0 s i) + mon 8 (uc q0 s k) + mon 10 (xc q0 s k i)) *
  (mon 5 (cc q1 s k i) + mon 0 (wc q1 s i) + mon 2 (zc q1 k)) *
  (mon 3 (bc q2 s k) + mon 4 (vc q2 k i) + mon 0 (yc q2 s i))

def p4 (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (i : Fin 5) : K[X] :=
  (mon 0 (ac q0 s i) - mon 4 ((11 : K) * ac q0 s i)) *
  mon 0 (wc q1 s i) * mon 0 (yc q2 s i)

def p5 (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (i : Fin 5) : K[X] :=
  -(mon 0 (ac q0 s i) + mon 8 (∑ k : Fin 11, uc q0 s k) +
      mon 10 (∑ k : Fin 11, xc q0 s k i)) *
  (mon 0 (wc q1 s i) + mon 6 (∑ k : Fin 11, zc q1 k) +
      mon 9 (∑ k : Fin 11, cc q1 s k i)) *
  (mon 0 (yc q2 s i) + mon 7 (∑ k : Fin 11, bc q2 s k) +
      mon 8 (∑ k : Fin 11, vc q2 k i))

def p6 (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (k : Fin 11) : K[X] :=
  -(mon 8 (uc q0 s k) + mon 4 (∑ i : Fin 5, ac q0 s i)) *
  (mon 2 (zc q1 k) + mon 0 (∑ i : Fin 5, wc q1 s i)) *
  (mon 3 (bc q2 s k) + mon 0 (∑ i : Fin 5, yc q2 s i))

def p7 (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) : K[X] :=
  (mon 0 (∑ i : Fin 5, ac q0 s i) + mon 8 (∑ k : Fin 11, uc q0 s k)) *
  (mon 0 (∑ i : Fin 5, wc q1 s i) + mon 6 (∑ k : Fin 11, zc q1 k)) *
  (mon 0 (∑ i : Fin 5, yc q2 s i) + mon 7 (∑ k : Fin 11, bc q2 s k))

def p8 (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) : K[X] :=
  (mon 4 ((11 : K) * ∑ i : Fin 5, ac q0 s i) -
      mon 0 (∑ i : Fin 5, ac q0 s i)) *
  mon 0 (∑ i : Fin 5, wc q1 s i) *
  mon 0 (∑ i : Fin 5, yc q2 s i)

def sidePoly (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) : K[X] :=
    (∑ i : Fin 5, ∑ k : Fin 11, p3 q0 q1 q2 s i k) +
    (∑ i : Fin 5, p4 q0 q1 q2 s i) +
    (∑ i : Fin 5, p5 q0 q1 q2 s i) +
    (∑ k : Fin 11, p6 q0 q1 q2 s k) +
    p7 q0 q1 q2 s + p8 q0 q1 q2 s

def fullPoly (q0 : Var0) (q1 : Var1) (q2 : Var2) : K[X] :=
  ∑ s : Fin 2, sidePoly q0 q1 q2 s

def residual (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) : K :=
  ∑ i : Fin 5, ∑ k : Fin 11, ac q0 s i * zc q1 k * vc q2 k i

def targetSide (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) : K :=
  ∑ i : Fin 5, ∑ k : Fin 11,
    (ac q0 s i * cc q1 s k i * bc q2 s k +
     uc q0 s k * wc q1 s i * vc q2 k i +
     xc q0 s k i * zc q1 k * yc q2 s i)

end

end PanLeanBridge

open MME PiTensorProduct BigOperators Finset Polynomial


namespace PanLeanBridge

set_option maxHeartbeats 12000000
set_option maxRecDepth 5000

variable {K : Type u} [Field K]

noncomputable section

abbrev Xobj : TensorObj K 3 :=
  TensorObj.bigAdd ![
    MMObj K 1 5 22,
    MMObj K 11 2 5,
    MMObj K 10 11 1]

abbrev X0 : TensorObj K 3 := MMObj K 1 5 22
abbrev X1 : TensorObj K 3 := MMObj K 11 2 5
abbrev X2 : TensorObj K 3 := MMObj K 10 11 1

def inc0 (r : Fin 3) : (X0 (K := K)).V r →ₗ[K] (Xobj (K := K)).V r :=
  LinearMap.inl K _ _

def inc1 (r : Fin 3) : (X1 (K := K)).V r →ₗ[K] (Xobj (K := K)).V r :=
  (LinearMap.inr K _ _).comp (LinearMap.inl K _ _)

def inc2 (r : Fin 3) : (X2 (K := K)).V r →ₗ[K] (Xobj (K := K)).V r :=
  (LinearMap.inr K _ _).comp (LinearMap.inr K _ _)

abbrev ModeIdx : Fin 3 → Type
  | ⟨0, _⟩ => (Fin 1 × Fin 5) ⊕ ((Fin 11 × Fin 2) ⊕ (Fin 10 × Fin 11))
  | ⟨1, _⟩ => (Fin 5 × Fin 22) ⊕ ((Fin 2 × Fin 5) ⊕ (Fin 11 × Fin 1))
  | ⟨2, _⟩ => (Fin 22 × Fin 1) ⊕ ((Fin 5 × Fin 11) ⊕ (Fin 1 × Fin 10))

def side5Equiv : (Fin 2 × Fin 5) ≃ Fin 10 := finProdFinEquiv
def side11Equiv : (Fin 2 × Fin 11) ≃ Fin 22 := finProdFinEquiv

def mode0Equiv : ModeIdx 0 ≃ Var0 where
  toFun
    | Sum.inl (_, i) => .a i
    | Sum.inr (Sum.inl (k, s)) => .u s k
    | Sum.inr (Sum.inr (si, k)) =>
        .x (side5Equiv.symm si).1 k (side5Equiv.symm si).2
  invFun
    | .a i => Sum.inl (0, i)
    | .u s k => Sum.inr (Sum.inl (k, s))
    | .x s k i => Sum.inr (Sum.inr (side5Equiv (s, i), k))
  left_inv
    | Sum.inl (h, i) => by fin_cases h; rfl
    | Sum.inr (Sum.inl (k, s)) => rfl
    | Sum.inr (Sum.inr (si, k)) => by simp
  right_inv q := by cases q <;> simp

def mode1Equiv : ModeIdx 1 ≃ Var1 where
  toFun
    | Sum.inl (i, sk) => .c (side11Equiv.symm sk).1 (side11Equiv.symm sk).2 i
    | Sum.inr (Sum.inl (s, i)) => .w s i
    | Sum.inr (Sum.inr (k, _)) => .z k
  invFun
    | .c s k i => Sum.inl (i, side11Equiv (s, k))
    | .w s i => Sum.inr (Sum.inl (s, i))
    | .z k => Sum.inr (Sum.inr (k, 0))
  left_inv
    | Sum.inl (i, sk) => by simp
    | Sum.inr (Sum.inl (s, i)) => rfl
    | Sum.inr (Sum.inr (k, h)) => by fin_cases h; rfl
  right_inv q := by cases q <;> simp

def mode2Equiv : ModeIdx 2 ≃ Var2 where
  toFun
    | Sum.inl (sk, _) => .b (side11Equiv.symm sk).1 (side11Equiv.symm sk).2
    | Sum.inr (Sum.inl (i, k)) => .v k i
    | Sum.inr (Sum.inr (_, si)) => .y (side5Equiv.symm si).1 (side5Equiv.symm si).2
  invFun
    | .b s k => Sum.inl (side11Equiv (s, k), 0)
    | .v k i => Sum.inr (Sum.inl (i, k))
    | .y s i => Sum.inr (Sum.inr (0, side5Equiv (s, i)))
  left_inv
    | Sum.inl (sk, h) => by fin_cases h; simp
    | Sum.inr (Sum.inl (i, k)) => rfl
    | Sum.inr (Sum.inr (h, si)) => by fin_cases h; simp
  right_inv q := by cases q <;> simp

noncomputable instance : Fintype Var0 := Fintype.ofEquiv (ModeIdx 0) mode0Equiv
noncomputable instance : Fintype Var1 := Fintype.ofEquiv (ModeIdx 1) mode1Equiv
noncomputable instance : Fintype Var2 := Fintype.ofEquiv (ModeIdx 2) mode2Equiv

def Var : Fin 3 → Type
  | ⟨0, _⟩ => Var0
  | ⟨1, _⟩ => Var1
  | ⟨2, _⟩ => Var2

noncomputable instance varFintype (r : Fin 3) : Fintype (Var r) :=
  match r with
  | ⟨0, _⟩ => inferInstanceAs (Fintype Var0)
  | ⟨1, _⟩ => inferInstanceAs (Fintype Var1)
  | ⟨2, _⟩ => inferInstanceAs (Fintype Var2)

instance varDecidableEq (r : Fin 3) : DecidableEq (Var r) :=
  match r with
  | ⟨0, _⟩ => inferInstanceAs (DecidableEq Var0)
  | ⟨1, _⟩ => inferInstanceAs (DecidableEq Var1)
  | ⟨2, _⟩ => inferInstanceAs (DecidableEq Var2)

noncomputable def modeBasis (s : Fin 3) : Module.Basis (Var s) K ((Xobj (K := K)).V s) :=
  match s with
  | ⟨0, _⟩ =>
      ((Pi.basisFun K (Fin 1 × Fin 5)).prod
        ((Pi.basisFun K (Fin 11 × Fin 2)).prod
          (Pi.basisFun K (Fin 10 × Fin 11)))).reindex mode0Equiv
  | ⟨1, _⟩ =>
      ((Pi.basisFun K (Fin 5 × Fin 22)).prod
        ((Pi.basisFun K (Fin 2 × Fin 5)).prod
          (Pi.basisFun K (Fin 11 × Fin 1)))).reindex mode1Equiv
  | ⟨2, _⟩ =>
      ((Pi.basisFun K (Fin 22 × Fin 1)).prod
        ((Pi.basisFun K (Fin 5 × Fin 11)).prod
          (Pi.basisFun K (Fin 1 × Fin 10)))).reindex mode2Equiv

noncomputable def tensorBasis :
    Module.Basis ((s : Fin 3) → Var s) K (PiTensorProduct K (Xobj (K := K)).V) :=
  Basis.piTensorProduct (modeBasis (K := K))

abbrev HalfSlot :=
  (Fin 5 × Fin 11) ⊕ (Fin 5 ⊕ (Fin 5 ⊕ (Fin 11 ⊕ (Fin 1 ⊕ Fin 1))))

abbrev Slot := Fin 2 × HalfSlot

noncomputable def slotEquiv : Slot ≃ Fin 156 :=
  (Fintype.equivFin Slot).trans (finCongr (by decide))

def hs3 (i : Fin 5) (k : Fin 11) : HalfSlot := Sum.inl (i, k)
def hs4 (i : Fin 5) : HalfSlot := Sum.inr (Sum.inl i)
def hs5 (i : Fin 5) : HalfSlot := Sum.inr (Sum.inr (Sum.inl i))
def hs6 (k : Fin 11) : HalfSlot := Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))
def hs7 : HalfSlot := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl 0))))
def hs8 : HalfSlot := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr 0))))

def factor0 (s : Fin 2) (h : HalfSlot) (q : Var0) : K[X] :=
  match h with
  | Sum.inl (i, k) =>
      mon 4 (ac q s i) + mon 8 (uc q s k) + mon 10 (xc q s k i)
  | Sum.inr (Sum.inl i) =>
      mon 0 (ac q s i) - mon 4 ((11 : K) * ac q s i)
  | Sum.inr (Sum.inr (Sum.inl i)) =>
      -(mon 0 (ac q s i) + mon 8 (∑ k, uc q s k) + mon 10 (∑ k, xc q s k i))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl k))) =>
      -(mon 8 (uc q s k) + mon 4 (∑ i, ac q s i))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))) =>
      mon 0 (∑ i, ac q s i) + mon 8 (∑ k, uc q s k)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) =>
      mon 4 ((11 : K) * ∑ i, ac q s i) - mon 0 (∑ i, ac q s i)

def factor1 (s : Fin 2) (h : HalfSlot) (q : Var1) : K[X] :=
  match h with
  | Sum.inl (i, k) =>
      mon 5 (cc q s k i) + mon 0 (wc q s i) + mon 2 (zc q k)
  | Sum.inr (Sum.inl i) => mon 0 (wc q s i)
  | Sum.inr (Sum.inr (Sum.inl i)) =>
      mon 0 (wc q s i) + mon 6 (∑ k, zc q k) + mon 9 (∑ k, cc q s k i)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl k))) =>
      mon 2 (zc q k) + mon 0 (∑ i, wc q s i)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))) =>
      mon 0 (∑ i, wc q s i) + mon 6 (∑ k, zc q k)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) =>
      mon 0 (∑ i, wc q s i)

def factor2 (s : Fin 2) (h : HalfSlot) (q : Var2) : K[X] :=
  match h with
  | Sum.inl (i, k) =>
      mon 3 (bc q s k) + mon 4 (vc q k i) + mon 0 (yc q s i)
  | Sum.inr (Sum.inl i) => mon 0 (yc q s i)
  | Sum.inr (Sum.inr (Sum.inl i)) =>
      mon 0 (yc q s i) + mon 7 (∑ k, bc q s k) + mon 8 (∑ k, vc q k i)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl k))) =>
      mon 3 (bc q s k) + mon 0 (∑ i, yc q s i)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))) =>
      mon 0 (∑ i, yc q s i) + mon 7 (∑ k, bc q s k)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) =>
      mon 0 (∑ i, yc q s i)

def factorPoly (slot : Slot) : ∀ r : Fin 3, Var r → K[X]
  | ⟨0, _⟩ => factor0 slot.1 slot.2
  | ⟨1, _⟩ => factor1 slot.1 slot.2
  | ⟨2, _⟩ => factor2 slot.1 slot.2

def slotPoly (slot : Slot) (q0 : Var0) (q1 : Var1) (q2 : Var2) : K[X] :=
  factor0 slot.1 slot.2 q0 * factor1 slot.1 slot.2 q1 * factor2 slot.1 slot.2 q2

end

end PanLeanBridge

open MME PiTensorProduct BigOperators Finset Polynomial


namespace PanLeanBridge

set_option maxHeartbeats 12000000
set_option maxRecDepth 5000

variable {K : Type u} [Field K]

noncomputable section

def liftFactor (r : Fin 3) (f : Var r → K[X]) : ℕ →₀ (Xobj (K := K)).V r :=
  ∑ q : Var r, (f q).toFinsupp.mapRange (fun c => c • modeBasis (K := K) r q) (by simp)

def vectorFactor (slot : Slot) (r : Fin 3) : ℕ →₀ (Xobj (K := K)).V r :=
  liftFactor r (factorPoly slot r)

def vfun (j : Fin 156) (r : Fin 3) : ℕ →₀ (Xobj (K := K)).V r :=
  vectorFactor (slotEquiv.symm j) r

noncomputable def vlin (r : Fin 3) (n : ℕ) :
    (TensorObj.diagObj K 3 156).V r →ₗ[K] (Xobj (K := K)).V r :=
  (Pi.basisFun K (Fin 156)).constr K (fun j => vfun j r n)

lemma vlin_support (r : Fin 3) :
    ∀ n : ℕ, vlin (K := K) r n ≠ 0 →
      n ∈ Finset.univ.biUnion (fun j : Fin 156 => (vfun (K := K) j r).support) := by
  intro n hne
  rw [Finset.mem_biUnion]
  by_contra hall
  push Not at hall
  apply hne
  have hz : (fun j : Fin 156 => (vfun (K := K) j r) n) =
      (0 : Fin 156 → (Xobj (K := K)).V r) :=
    funext fun j => Finsupp.notMem_support_iff.mp (hall j (Finset.mem_univ j))
  show (Pi.basisFun K (Fin 156)).constr K (fun j => (vfun j r) n) = 0
  rw [hz]
  exact map_zero _

noncomputable def Phi : PolyFamily (Xobj (K := K)) (TensorObj.diagObj K 3 156) where
  A := fun r => Finsupp.onFinset _ _ (vlin_support r)

end

end PanLeanBridge

open MME PiTensorProduct BigOperators Finset Polynomial

namespace PanLeanBridge

set_option maxHeartbeats 12000000
set_option maxRecDepth 5000

variable {K : Type u} [Field K]

noncomputable section

def pureABC (s : Fin 2) (i : Fin 5) (k : Fin 11) :
    PiTensorProduct K (Xobj (K := K)).V :=
  tprod K (fun r => match r with
    | ⟨0, _⟩ => modeBasis (K := K) 0 (.a i)
    | ⟨1, _⟩ => modeBasis (K := K) 1 (.c s k i)
    | ⟨2, _⟩ => modeBasis (K := K) 2 (.b s k))

def pureUWV (s : Fin 2) (i : Fin 5) (k : Fin 11) :
    PiTensorProduct K (Xobj (K := K)).V :=
  tprod K (fun r => match r with
    | ⟨0, _⟩ => modeBasis (K := K) 0 (.u s k)
    | ⟨1, _⟩ => modeBasis (K := K) 1 (.w s i)
    | ⟨2, _⟩ => modeBasis (K := K) 2 (.v k i))

def pureXZY (s : Fin 2) (i : Fin 5) (k : Fin 11) :
    PiTensorProduct K (Xobj (K := K)).V :=
  tprod K (fun r => match r with
    | ⟨0, _⟩ => modeBasis (K := K) 0 (.x s k i)
    | ⟨1, _⟩ => modeBasis (K := K) 1 (.z k)
    | ⟨2, _⟩ => modeBasis (K := K) 2 (.y s i))

def targetTensor : PiTensorProduct K (Xobj (K := K)).V :=
  ∑ s : Fin 2, ∑ i : Fin 5, ∑ k : Fin 11,
    (pureABC (K := K) s i k + pureUWV (K := K) s i k + pureXZY (K := K) s i k)

end

end PanLeanBridge


