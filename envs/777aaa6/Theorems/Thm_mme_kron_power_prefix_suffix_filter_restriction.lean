-- Prove2me | Theorems.Thm_mme_kron_power_prefix_suffix_filter_restriction
-- name    : mme_kron_power_prefix_suffix_filter_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T05:22:44.553517+00:00
-- url     : https://prove2.me/theorems/e1833879-dcf5-435b-8cbf-0be9142f78ff
-- title:
--   Two half-power filters become prefix and suffix filters
-- statement:
--   Let $T$ be a three-mode tensor over a field $K$, and let $m,n\ge0$. Choose bases for modes 0 and 1, a predicate $P$ on mode-0 words of length $m$, and a predicate $Q$ on mode-1 words of length $n$. Let $X$ be $T^{\otimes m}$ with mode 0 filtered by $P$, and let $Y$ be $T^{\otimes n}$ with mode 1 filtered by $Q$. In $T^{\otimes(n+m)}$, retain the mode-0 words whose first $m$ coordinates satisfy $P$ and the mode-1 words whose last $n$ coordinates satisfy $Q$; call this tensor $Z$. Then
--   $$Z\preceq X\otimes Y,$$
--   where $\preceq$ denotes tensor restriction. Mode 2 remains unfiltered. This transports two separate word filters to coordinate blocks of a single power without imposing any additional condition on the predicates.
-- source:
--   Coordinate-preserving concatenation of tensor powers and the common-halving unpermuted source restriction.

import Theorems.Thm_mme_kron_power_concatenation_basis_transport
import Definitions.Def_mme_tensor_rank

open MME MME.DWZComponentRestriction Module TensorProduct PiTensorProduct
universe u
set_option autoImplicit false

theorem mme_kron_power_prefix_suffix_filter_restriction
    {K : Type u} [Field K] (T : TensorObj K 3) (n m : ℕ)
    {α β : Type u} (bX : Basis α K (T.V 0)) (bY : Basis β K (T.V 1))
    (P : (Fin m → α) → Prop) (Q : (Fin n → β) → Prop)
    [DecidablePred P] [DecidablePred Q] :
    let X := T.kronPow m
    let Y := T.kronPow n
    let Z := T.kronPow (n + m)
    let bx := kronPowModeBasis T 0 bX m
    let basisY := kronPowModeBasis T 1 bY n
    let bzX := kronPowModeBasis T 0 bX (n + m)
    let bzY := kronPowModeBasis T 1 bY (n + m)
    let f : ∀ i, X.V i →ₗ[K] X.V i := Function.update (fun _ => LinearMap.id) 0
      (bx.constr K (fun w => if P (PowIndex.get m w) then bx w else 0))
    let g : ∀ i, Y.V i →ₗ[K] Y.V i := Function.update (fun _ => LinearMap.id) 1
      (basisY.constr K (fun w => if Q (PowIndex.get n w) then basisY w else 0))
    let h : ∀ i, Z.V i →ₗ[K] Z.V i := Function.update
      (Function.update (fun _ => LinearMap.id) 0
        (bzX.constr K (fun w =>
          if P (fun r => PowIndex.get (n + m) w ⟨r.val, by omega⟩) then bzX w else 0))) 1
      (bzY.constr K (fun w =>
        if Q (fun r => PowIndex.get (n + m) w ⟨m + r.val, by omega⟩) then bzY w else 0))
    TensorObj.Restrict { Z with t := PiTensorProduct.map h Z.t }
      (TensorObj.kron { X with t := PiTensorProduct.map f X.t }
        { Y with t := PiTensorProduct.map g Y.t }) := by sorry
