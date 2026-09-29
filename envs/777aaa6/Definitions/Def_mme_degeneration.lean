-- Prove2me | Definitions.Def_mme_degeneration
-- name    : mme_degeneration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-28T20:38:00.407926+00:00
-- url     : https://prove2.me/theorems/ee0d8d8f-6377-45f3-9ae4-f595c0dbc6e1
-- statement:
--   **Degeneration (border rank) for order-$d$ tensor objects.**
--
--   Fix a field $K$ and concrete order-$d$ tensor objects $X$ and $Y$, each consisting of finite-dimensional mode spaces together with a structure tensor. A *polynomial family* from $Y$ to $X$ assigns to every mode $i$ a finitely supported sequence of linear maps $A_i(0),A_i(1),\dots\colon Y_i\to X_i$, viewed as the coefficients of a formal parameter $\varepsilon$. Substituting $A_i(\varepsilon)=\sum_j A_i(j)\,\varepsilon^{\,j}$ into the $i$-th leg for every mode and expanding, the degree-$k$ coefficient of the family applied to $Y$'s structure tensor $y$ is
--
--   $$
--   \Phi_k\;=\;\sum_{j_1+\cdots+j_d=k}\bigl(A_1(j_1)\otimes\cdots\otimes A_d(j_d)\bigr)(y).
--   $$
--
--   The tensor $X$ *degenerates from* $Y$ *of order* $h$ when some polynomial family satisfies $\Phi_k=0$ for every $k<h$ and $\Phi_h=x$, the structure tensor of $X$; the unqualified degeneration relation quantifies the order $h$ existentially. Taking $Y=I_r$, the order-$d$ diagonal unit tensor with $r$ slots, the relation says exactly that $X$ has **border rank** at most $r$ — $X$ is realized as the leading coefficient of an $\varepsilon$-family of tensors of rank at most $r$, uniformly over an arbitrary field.
--
--   Border rank is the quantity controlled by approximate bilinear algorithms, and this predicate is the interface through which every such construction enters the development: a degeneration from $I_r$ is converted into an asymptotic-rank bound (`mme_degenerates_asymptoticRank_le`) and then fed to Schönhage's asymptotic sum inequality to bound the matrix-multiplication exponent.
--
--   **Formalization Note** The development is concrete on `TensorObj` — no passage to isomorphism classes — following the Strassen/Wigderson–Zuiddam presentation. In `Degenerates X Y` the *first* argument is the target and the *second* is the source: `Degenerates X (TensorObj.diagObj K d r)` reads "$X$ has border rank at most $r$". `DegeneratesOfOrder X Y h` fixes the leading order $h$; `Degenerates` hides it behind an existential.
-- source:
--   https://www.math.ias.edu/~avi/PUBLICATIONS/WigdersonZu_Final_Draft_Oct2023.pdf

import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Definitions.Def_mme_tensor

/-! # Degeneration (border rank) of tensor objects

A *polynomial family* `Φ` assigns to each mode `i` a finitely-supported family of
linear maps `Y.V i →ₗ X.V i`, one per power of a formal parameter `ε`. Its degree-`k`
coefficient `Φ.coeff k` is `∑_{∑ jᵢ = k} (⨂ᵢ Φ.A i (jᵢ)) (Y.t)`.

`X` **degenerates** from `Y` of order `h` (`DegeneratesOfOrder X Y h`) when some `Φ`
has all coefficients below `h` vanishing and degree-`h` coefficient `X.t`. With `Y` the
diagonal unit `I_r`, this is exactly "`X` has border rank `≤ r`". Border rank refines
ordinary rank and is the quantity Schönhage's construction controls. Concrete on
`TensorObj` (no quotient), following the Prism/Strassen development. -/

universe u

open PiTensorProduct BigOperators

namespace MME

variable {K : Type u} [Field K] {d : ℕ}

/-- A polynomial family of mode-wise linear maps `Y.V i →ₗ X.V i`, finitely supported
in the formal parameter's degree. -/
structure PolyFamily (X Y : TensorObj K d) where
  A : ∀ i, ℕ →₀ (Y.V i →ₗ[K] X.V i)

namespace PolyFamily

variable {X Y : TensorObj K d}

/-- The degree-`k` coefficient `∑_{∑ jᵢ = k} (⨂ᵢ A i (jᵢ)) (Y.t)`. -/
noncomputable def coeff (Φ : PolyFamily X Y) (k : ℕ) : PiTensorProduct K X.V :=
  (Finset.Nat.antidiagonalTuple d k).sum
    (fun j => PiTensorProduct.map (fun i => Φ.A i (j i)) Y.t)

/-- A plain restriction `f`, viewed as a polynomial family supported at degree `0`. -/
noncomputable def ofRestrict (f : ∀ i, Y.V i →ₗ[K] X.V i) : PolyFamily X Y where
  A := fun i => Finsupp.single 0 (f i)

end PolyFamily

/-- `X` degenerates from `Y` of order `h`: a polynomial family with coefficients below
`h` vanishing and degree-`h` coefficient `X.t`. -/
def DegeneratesOfOrder (X Y : TensorObj K d) (h : ℕ) : Prop :=
  ∃ Φ : PolyFamily X Y, (∀ k, k < h → Φ.coeff k = 0) ∧ Φ.coeff h = X.t

/-- `X` degenerates from `Y` at some order (border restriction). -/
def Degenerates (X Y : TensorObj K d) : Prop :=
  ∃ h, DegeneratesOfOrder X Y h

end MME


