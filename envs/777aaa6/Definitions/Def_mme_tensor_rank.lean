-- Prove2me | Definitions.Def_mme_tensor_rank
-- name    : mme_tensor_rank
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-05-28T14:36:20.754383+00:00
-- url     : https://prove2.me/theorems/eda9cf2a-ddbd-4735-a60a-acff881c5170
-- statement:
--   **Restriction, tensor rank, asymptotic rank, and the matrix-multiplication tensor object.**
--
--   Fix a field $K$ and order-$d$ tensor objects $X$ and $Y$. The *restriction preorder* $X\le Y$ (Strassen) holds when there are linear maps, one per mode, carrying $Y$'s structure tensor to $X$'s. Writing $I_r$ for the order-$d$ diagonal unit tensor with $r$ slots, the *tensor rank* of $X$ is
--
--   $$
--   R(X)\;=\;\min\{\,r \;:\; X\le I_r\,\},
--   $$
--
--   which agrees with the textbook least number of simple tensors summing to $X$. The *asymptotic rank* of $X$ is the amortized rank over Kronecker powers, $\inf_n R\!\left(X^{\boxtimes n}\right)^{1/n}$, taken as a real number.
--
--   The module also packages matrix multiplication as an order-3 tensor object: $\langle n,m,p\rangle=\sum_{i,j,k}e_{ij}\otimes e_{jk}\otimes e_{ki}$, the tensor of the bilinear map multiplying an $n\times m$ matrix by an $m\times p$ matrix.
--
--   These are the load-bearing interfaces of the exponent series: border-rank constructions bound the asymptotic rank of direct sums of $\langle n,m,p\rangle$'s, and the asymptotic sum inequality turns such bounds into bounds on $\omega$.
--
--   **Formalization Note** Provides `TensorObj.Restrict`, `tensorRankObj`, `tensorAsymptoticRank` (defined as $\inf_n R(X^{\otimes(n+1)})^{1/(n+1)}$ so the index is always positive), and `MMObj K n m p : TensorObj K 3`, reusing `MMSpace`/`MMTensor` from `mme_omega`. Imports `Def_mme_tensor` and `Def_mme_omega`.
-- source:
--   https://www.math.ias.edu/~avi/PUBLICATIONS/WigdersonZu_Final_Draft_Oct2023.pdf

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Definitions.Def_mme_tensor
import Definitions.Def_mme_omega

/-! # Restriction, tensor rank, asymptotic rank, and the MM object

Restriction (Strassen's preorder between tensor objects), the concrete tensor rank
`tensorRankObj X = min { r | X ≤ I_r }`, the asymptotic tensor rank
`tensorAsymptoticRank X = inf_n rank(X^⊗ⁿ)^(1/n)`, and the matrix-multiplication tensor
`MMObj n m p` packaged as a `TensorObj K 3`. -/

universe u

open PiTensorProduct TensorProduct BigOperators

namespace MME

variable {K : Type u} [Field K] {d : ℕ}

/-- **Restriction.** `X` is a restriction of `Y` (`X ≤ Y` in Strassen's preorder) if
there are linear maps `f_i : Y.V i → X.V i` whose tensor product sends `Y.t` to `X.t`.

Namespaced under `TensorObj` to avoid clashing with the raw-tensor `Restrict` of
`Def_mme_omega_strassen`. -/
def TensorObj.Restrict (X Y : TensorObj K d) : Prop :=
  ∃ f : ∀ i, Y.V i →ₗ[K] X.V i, PiTensorProduct.map f Y.t = X.t

/-- **Tensor rank** of a tensor object: the least `r` for which `X` is a restriction of
the diagonal unit tensor `I_r`. (Coincides with the textbook decomposition rank.) -/
noncomputable def tensorRankObj (X : TensorObj K d) : ℕ :=
  sInf {r | TensorObj.Restrict X (TensorObj.diagObj K d r)}

/-- **Asymptotic tensor rank** `inf_n rank(X^⊗(n+1))^(1/(n+1))`. -/
noncomputable def tensorAsymptoticRank (X : TensorObj K d) : ℝ :=
  ⨅ n : ℕ, (tensorRankObj (TensorObj.kronPow X (n + 1)) : ℝ) ^ ((1 : ℝ) / (n + 1))

/-- The matrix-multiplication tensor `⟨n,m,p⟩ = ∑_{i,j,k} e_{ij} ⊗ e_{jk} ⊗ e_{ki}`
packaged as an order-3 tensor object. Reuses `MMSpace`/`MMTensor` from `mme_omega`. -/
noncomputable def MMObj (K : Type u) [Field K] (n m p : ℕ) : TensorObj K 3 where
  V := MMSpace K n m p
  fin := fun i => by
    match i with
    | ⟨0, _⟩ => exact inferInstance
    | ⟨1, _⟩ => exact inferInstance
    | ⟨2, _⟩ => exact inferInstance
  t := MMTensor K n m p

end MME


